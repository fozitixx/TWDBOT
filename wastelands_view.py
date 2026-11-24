"""Screen recognition and conversion between the shared map and one RDP view."""
import base64
import io
import json
import math
from functools import lru_cache
from itertools import permutations
from pathlib import Path
import subprocess

import numpy as np
from PIL import Image, ImageDraw, ImageFilter

try:
    import cv2
except (ImportError, OSError):
    cv2 = None


ANCHOR = np.array([835., 475.])


def color_boxes(mask):
    if cv2 is not None:
        contours, _ = cv2.findContours(mask, cv2.RETR_LIST, cv2.CHAIN_APPROX_SIMPLE)
        return [cv2.boundingRect(contour) for contour in contours]
    # A UI border and the space enclosed by it can each delimit a card.
    boxes = []
    for foreground in (mask, 1-mask):
        runs = np.diff(np.pad(foreground, ((0, 0), (1, 1))).astype(np.int8), axis=1)
        parents, bounds, previous = [], [], []

        def root(i):
            while parents[i] != i:
                parents[i] = parents[parents[i]]
                i = parents[i]
            return i

        for y, row in enumerate(runs):
            current = []
            index = 0
            for left, right in zip(np.flatnonzero(row == 1), np.flatnonzero(row == -1)):
                node = len(parents)
                parents.append(node)
                bounds.append((left, y, right, y+1))
                while index < len(previous) and previous[index][1] < left:
                    index += 1
                j = index
                while j < len(previous) and previous[j][0] <= right:
                    parents[root(previous[j][2])] = node
                    j += 1
                current.append((left, right, node))
            previous = current
        merged = {}
        for i, (left, top, right, bottom) in enumerate(bounds):
            key = root(i)
            x, y, r, b = merged.get(key, (left, top, right, bottom))
            merged[key] = (min(x,left), min(y,top), max(r,right), max(b,bottom))
        boxes.extend((x,y,r-x,b-y) for x,y,r,b in merged.values())
    return boxes


def invite_buttons(img):
    """Find adjacent decline/accept rectangles in the top-right invitation."""
    w, h = img.size
    left, top = int(.68*w), int(.08*h)
    rgb = np.asarray(img.crop((left,top,w,int(.43*h))).convert("RGB"), dtype=np.int16)
    r,g,b = rgb.transpose(2,0,1)
    def buttons(mask):
        return [(x+left,y+top,bw,bh) for x,y,bw,bh in color_boxes(mask.astype(np.uint8))
                if .035*w < bw < .115*w and .018*h < bh < .075*h and 1.8 < bw/bh < 5]
    red = buttons((r>110)&(r>1.6*g)&(r>1.4*b))
    green = buttons((g>95)&(g>1.6*r)&(g>1.4*b))
    for x,y,rw,rh in sorted(red,key=lambda box:-box[2]*box[3]):
        for gx,gy,gw,gh in sorted(green,key=lambda box:-box[2]*box[3]):
            if (0 <= gx-x-rw < .35*rh and abs(gy-y)<.18*rh and
                    .83*rh<gh<1.2*rh and .9*rw<gw<1.6*rw):
                return (x,y,gx+gw,rh), ((gx+gw/2)/w,(gy+gh/2)/h)
    return None


# Cyan text of the map name in the compact Roblox invitation at 1366px.
_WASTELAND_WORD = np.array([[c == "#" for c in row] for row in (
    "...........................#................#",
    "##..##..#..........#.......#................#",
    ".#..##..#.###...#####..##..#.###..####...####",
    ".#.###.##...##.#..##..##.#.#...##.##.#..##.##",
    ".###.###..####.#####..####.#.####.#..#..#...#",
    "..##..##..####...###..##.#.#.####.#..#..##.##",
    "..##..##..####.######..###.#.####.#..#...####",
)])


def _wasteland_word(img, x, y, right, height):
    # The invitation prefix is white. Compare the full cyan word, including
    # its proportions, so a different destination cannot match by a substring.
    region = img.crop((x, y-round(.63*height), right, y-round(.08*height)))
    r, g, b = np.asarray(region.convert("RGB"), dtype=np.int16).transpose(2, 0, 1)
    ink = (g-r > 25) & (b-r > 45) & (g > 106) & (b > 140)
    rows, cols = np.nonzero(ink)
    if not rows.size:
        return False
    word = ink[rows.min():rows.max()+1, cols.min():cols.max()+1]
    h, w = word.shape
    th, tw = _WASTELAND_WORD.shape
    if abs((w/h)/(tw/th)-1) > .18:
        return False
    scaled = Image.fromarray(word.astype(np.uint8)*255).resize((tw, th), Image.Resampling.BOX)
    mask = np.asarray(scaled) >= 128
    return np.count_nonzero(mask & _WASTELAND_WORD) >= .72*np.count_nonzero(mask | _WASTELAND_WORD)


def read_invite(img, host, read):
    pair = invite_buttons(img)
    if pair is None:
        return None, ""
    (x,y,right,height), button = pair
    def line(high,low):
        box = ((x-.10*height)/img.width,(y-high*height)/img.height,
               right/img.width,(y-low*height)/img.height)
        return read(img,box,zoom=5)
    if not label(line(1.29,.56),host):
        return None, "Вижу приглашение · имя отправителя не совпало или не прочитано"
    if _wasteland_word(img, x, y, right, height):
        return button, ""
    words = line(.62,.07)
    if not any(label(words, text) for name in ("Wasteland","Wastelands")
               for text in (name, "to"+name, "invited you to "+name)):
        return None, "Вижу приглашение от основы · не распознана карта Wasteland"
    return button, ""


def _binary_match(template, spectrum, integral, shape):
    """Normalized correlation of binary images over fully visible placements."""
    h, w = template.shape
    totals = integral[h:,w:] - integral[:-h,w:] - integral[h:,:-w] + integral[:-h,:-w]
    freq = np.fft.rfft2(template, s=shape, axes=(0,1))
    hits = np.fft.irfft2(spectrum * freq.conj(), s=shape, axes=(0,1))
    area = template.size
    count = float(template.sum())
    norm = np.sqrt(totals*(1-totals/area) * count*(1-count/area))
    covariance = hits[:totals.shape[0], :totals.shape[1]] - totals*(count/area)
    scores = np.divide(covariance, norm, out=np.zeros_like(covariance), where=norm>0)
    y,x = np.unravel_index(scores.argmax(), scores.shape)
    return scores[y,x], (x,y)


def mission_button(img, mode):
    """Match the aligned red and purple button outlines even when a card is black."""
    w = 640
    h = round(w*img.height/img.width)
    top = int(.63*h)
    band = img.convert("RGB").resize((w,h),Image.Resampling.BILINEAR).crop((0,top,w,int(.80*h)))
    r,g,b = np.asarray(band,dtype=np.int16).transpose(2,0,1)
    def buttons(mask):
        return [(x,y+top,bw,bh) for x,y,bw,bh in color_boxes(mask.astype(np.uint8))
                if .09*w<bw<.20*w and .035*h<bh<.085*h and 0<y<band.height-bh]
    red = buttons((r>92)&(r>2*g+8)&(r>1.45*b))
    purple = buttons((b>92)&(b>2*g+10)&(b>1.25*r))
    for left in red:
        for right in purple:
            x,y,bw,bh = left
            rx,ry,rw,rh = right
            if (.32*w<x<.43*w and .50*w<rx<.57*w and 0<rx-x-bw<.055*w and
                    abs(y+bh/2-ry-rh/2)<.01*h and .8<bw/rw<1.25):
                x,y,bw,bh = right if mode=="nightmare" else left
                return dict(cx=(x+bw/2)/w,cy=(y+bh/2)/h,w=bw/w,h=bh/h)
    return None


@lru_cache(maxsize=1)
def _counter_glyphs():
    # Reference masks in game font order: 0, 1, 2, 3, 4, slash.
    with Image.open(Path(__file__).with_name("wastelands_digits.png")) as atlas:
        return np.stack([np.asarray(atlas.crop((x,0,x+24,32)))>=128 for x in range(0,144,24)])


def visual_slot_count(mask,limit):
    """Read three outlined glyphs on one card; require the correct denominator."""
    refs = _counter_glyphs()
    work = mask.copy()
    glyphs = []
    component_lut = [255 if i==128 else 0 for i in range(256)]
    while (area := work.getbbox()) is not None:
        left,top,right,_ = area
        start = work.crop((left,top,right,top+1)).getbbox()[0]
        ImageDraw.floodfill(work,(left+start,top),128)
        component = work.point(component_lut)
        work.paste(0,mask=component)
        x,y,r,b = component.getbbox()
        h,w = b-y,r-x
        if not (.24*mask.height<=h<=.78*mask.height and .20*h<=w<=1.18*h):
            continue
        sample = np.asarray(component.crop((x,y,r,b)).resize((24,32),Image.Resampling.BILINEAR))>=128
        scores = (refs & sample).sum(axis=(1,2))/(refs | sample).sum(axis=(1,2))
        runner,best = np.argsort(scores)[-2:]
        if scores[best]>=.65 and scores[best]-scores[runner]>=.075:
            glyphs.append((int(best),x,r,(y+b)/2,h))
    results = set()
    for slash,sx,sr,sy,sh in glyphs:
        if slash!=5:
            continue
        for number,x,r,y,h in glyphs:
            if number>limit or not (-.1*h<=sx-r<=.38*h and abs(y-sy)<.28*h):
                continue
            for digit,dx,dr,dy,dh in glyphs:
                if (digit==limit and -.12*h<=dx-sr<=.38*h and abs(y-dy)<.20*h
                        and .72*h<=dh<=1.35*h and .9*h<=sh<=1.8*h
                        and .25*mask.width<(x+dr)/2<.77*mask.width):
                    results.add(number)
    return results.pop() if len(results)==1 else None


@lru_cache(maxsize=1)
def _hotbar_portraits():
    with Image.open(Path(__file__).with_name("wastelands_hotbar.png")) as strip:
        return np.stack([np.asarray(strip.crop((x,0,x+32,32)),dtype=np.int16)
                         for x in range(0,128,32)])


def wastelands_slots(img):
    """Recognize a complete loadout. Keep manual slots for unknown skins or partial matches."""
    refs = _hotbar_portraits()
    names = ("amplifier","screen","plunger","tv")
    scores = np.full((4,6),255.)
    w,h = img.size
    # Ignore the hover counter and the slot number in the top-left corner.
    mask = np.ones((32,32),dtype=bool)
    mask[10:23] = False
    mask[:8,:8] = False
    templates = refs[:,mask].reshape(4,-1).astype(float)
    templates -= templates.mean(axis=1,keepdims=True)
    norm = np.linalg.norm(templates,axis=1)
    for slot in range(6):
        nominal = w*.5 + (slot-2.5)*.13*h
        for shift in (-.01,0,.005,.01,.015):
            x = nominal + shift*h
            for y in (.874*h,.880*h):
                box = tuple(round(v) for v in (x-.033*h,y-.034*h,x+.033*h,y+.034*h))
                crop = img.crop(box).convert("RGB").resize((32,32),Image.Resampling.BILINEAR)
                diff = np.abs(refs - np.asarray(crop,dtype=np.int16))
                pixels = np.asarray(crop)[mask].ravel().astype(float)
                pixels -= pixels.mean()
                corr = templates @ pixels / np.maximum(1,norm*np.linalg.norm(pixels))
                cost = diff[:,mask].mean(axis=(1,2)) + 28*(1-corr)
                scores[:,slot] = np.minimum(scores[:,slot],cost)
    slots = scores.argmin(axis=1)
    ranked = np.sort(scores,axis=1)
    if len(set(slots))==4 and np.all(ranked[:,0]<34) and np.all(ranked[:,1]-ranked[:,0]>6):
        return {name:int(slot)+1 for name,slot in zip(names,slots)}
    return None


def ready_button(img):
    w,h = img.size
    left,top = round(.37*w),round(.12*h)
    roi = img.crop((left,top,round(.63*w),round(.27*h))).convert("RGB")
    r,g,b = np.asarray(roi,dtype=np.int16).transpose(2,0,1)
    green = (g>65)&(g-r>45)&(g-b>45)
    for x,y,bw,bh in sorted(color_boxes(green.astype(np.uint8)),key=lambda box:-box[2]*box[3]):
        if not (.07*w<bw<.15*w and .035*h<bh<.09*h and abs(left+x+bw/2-w/2)<.035*w):
            continue
        if green[y:y+bh,x:x+bw].mean()>.60:
            return dict(cx=(left+x+bw/2)/w,cy=(top+y+bh/2)/h,w=bw/w,h=bh/h)
    return None


# Centers of three separate olive vehicles around the annotated early-defense bend.
_VEHICLES = np.array([[804.,700.],[505.,515.],[1248.,275.]])
_LANDMARK_BASIS = np.linalg.inv((_VEHICLES[:2]-ANCHOR).T)


def landmark_pose(img):
    """Determine which bend is visible using two wrecks and the branching road."""
    w = 512
    h = round(w*img.height/img.width)
    rgb = np.asarray(img.convert("RGB").resize((w,h),Image.Resampling.BILINEAR),dtype=np.int16)
    r,g,b = rgb.transpose(2,0,1)
    olive = (abs(r-g)<=6)&(g-b>10)&(g<112)&(g>30)
    olive = np.asarray(Image.fromarray(olive).filter(ImageFilter.MedianFilter(3)),dtype=np.uint8)
    centers = [(x+bw/2,y+bh/2) for x,y,bw,bh in color_boxes(olive)
               if 9<=bw<=52 and 6<=bh<=46 and bw*bh>=108 and y+bh/2<.83*h
               and olive[y:y+bh,x:x+bw].mean()>.35]
    if not 2<=len(centers)<=50:
        return None
    road = (r>110)&(r-g>58)&(r-b>52)
    road = np.asarray(Image.fromarray(road).filter(ImageFilter.MaxFilter(3)))
    # Sample both sides of the junction and the first side road separately.
    edges = [((450,212),(815,461)),((855,489),(1370,838)),((835,475),(990,246)),
             ((990,246),(805,125)),((1550,965),(1430,1149))]
    samples = np.array([np.linspace(a,b,21) for a,b in edges])-ANCHOR
    shifts = np.stack(np.meshgrid(np.arange(-20,21,2),np.arange(-20,21,2)),axis=-1).reshape(-1,2)
    ref_delta = complex(*(_VEHICLES[1]-_VEHICLES[0]))
    matches = []
    for pair in permutations(centers,2):
        a,second = np.asarray(pair)
        ratio = complex(*(second-a))/ref_delta
        if not .16<abs(ratio)<.38:
            continue
        anchor = complex(*a)+ratio*complex(*(ANCHOR-_VEHICLES[0]))
        origins = np.array([anchor.real,anchor.imag])+shifts
        mats = (np.asarray(pair)[None,:,:]-origins[:,None,:]).transpose(0,2,1)@_LANDMARK_BASIS
        spawn = origins+mats@(np.array([1024,576])-ANCHOR)
        good = (abs(spawn[:,0]-w/2)<.16*w)&(abs(spawn[:,1]-h/2)<.19*h)
        if not good.any():
            continue
        origins,mats = origins[good],mats[good]
        points = origins[:,None,None,:]+np.einsum("nij,ekj->neki",mats,samples)
        x,y = np.rint(points).astype(int).transpose(3,0,1,2)
        visible = (x>=0)&(x<w)&(y>=0)&(y<h)&~((y>.81*h)&(x>.26*w)&(x<.74*w))
        visible &= ~((y<.23*h)&(x>.33*w)&(x<.67*w))
        yy,xx = y.clip(0,h-1),x.clip(0,w-1)
        # Ignore brightly painted overlays (including map annotations) that hide the road.
        visible &= ~((g[yy,xx]>210)&(b[yy,xx]<65))
        hit = visible & road[yy,xx]
        n = visible.sum(2)
        support = hit.sum(2)/np.maximum(1,n)
        good = ((n[:,:3]>=7)&(support[:,:3]>=.58)).all(1)
        scores = hit[:,:3].sum((1,2))/np.maximum(1,n[:,:3].sum(1))
        scores += .06*(hit[:,3:].sum((1,2))/np.maximum(1,n[:,3:].sum(1))-.5)
        # Smaller corrections to the initial similarity fit break ties within a road stripe.
        scores -= .025*np.linalg.norm(origins-[anchor.real,anchor.imag],axis=1)/20
        scores[~good] = 0
        idx = scores.argmax()
        if scores[idx]>=.76:
            matches.append((scores[idx],origins[idx],mats[idx]))
    if not matches:
        return None
    matches.sort(key=lambda entry:-entry[0])
    score,origin,mat = matches[0]
    for other,loc,transform in matches[1:]:
        if score-other>.07:
            break
        if np.linalg.norm(origin-loc)>7 or np.linalg.norm(mat-transform)>.045:
            return None
    return origin/[w,h], mat/np.array([[w],[h]])


def placement_pose(img):
    landmarks = landmark_pose(img)
    if landmarks is None:
        return None
    road = road_pose(img)
    if road is not None:
        # Use the more precise road fit only when the wrecks verify its orientation.
        offsets = np.asarray([screen_point(road,p) for p in _VEHICLES])-np.asarray(
            [screen_point(landmarks,p) for p in _VEHICLES])
        if np.max(np.linalg.norm(offsets*img.size,axis=1))<.024*img.width:
            return road
    return landmarks


def road_pose(img):
    """Match the bend and diagonal of the marked map independently on every client."""
    w = 360
    h = round(w * img.height/img.width)
    rgb = np.asarray(img.convert("RGB").resize((w,h),Image.Resampling.BILINEAR)).astype(np.int16)
    r,g,b = rgb.transpose(2,0,1)
    mask = ((r>110)&(r-g>58)&(r-b>52)).astype(np.uint8)
    mask[int(.81*h):,int(.26*w):int(.74*w)] = 0
    mask[:int(.14*h),int(.31*w):int(.67*w)] = 0
    if mask.mean() < .014:
        return None
    if cv2 is None:
        shape = (math.ceil(h/32)*32, w)
        spectrum = np.fft.rfft2(mask, s=shape, axes=(0,1))
        integral = np.pad(mask.cumsum(0,dtype=np.int32).cumsum(1,dtype=np.int32), ((1,0),(1,0)))
    # Lines entering/leaving the junction, including the second bend above it.
    edges = [((570,295),(1085,645)), ((835,475),(990,246)), ((990,246),(805,125))]
    best = None
    for zoom in (.82,.91,1.,1.10,1.21):
        k = w/2048*zoom
        for angle in range(-180,180,6):
            rad = math.radians(angle)
            mat = k*np.array([[math.cos(rad),-math.sin(rad)],[math.sin(rad),math.cos(rad)]])
            pts = (np.asarray(edges)-ANCHOR) @ mat.T
            lo = np.floor(pts.min(axis=(0,1))-5).astype(int)
            hi = np.ceil(pts.max(axis=(0,1))+5).astype(int)
            width, height = hi-lo+1
            if width>w or height>h:
                continue
            lines = np.rint(pts-lo).astype(int).tolist()
            stroke = max(3,round(46*k))
            if cv2 is None:
                template = Image.new("L", (width, height))
                draw = ImageDraw.Draw(template)
                for a,bp in lines:
                    draw.line((tuple(a),tuple(bp)), fill=1, width=stroke)
                score,xy = _binary_match(np.asarray(template), spectrum, integral, shape)
            else:
                template = np.zeros((height,width),np.uint8)
                for a,bp in lines:
                    cv2.line(template,tuple(a),tuple(bp),1,stroke)
                scores = cv2.matchTemplate(mask,template,cv2.TM_CCOEFF_NORMED)
                _,score,_,xy = cv2.minMaxLoc(scores)
            if best is None or score>best[0]:
                best = score, np.asarray(xy)-lo, mat
    if best is None or best[0] < .62:
        return None
    _, origin, mat = best
    # Sample transverse road sections. The two parallel stretches constrain
    # scale; the bend and diagonal constrain rotation and translation.
    for _ in range(3):
        rows,centers = [],[]
        for a,b in edges + [((835,475),(1740,1090)),((1550,965),(1430,1149))]:
            a,b = np.asarray(a)-ANCHOR,np.asarray(b)-ANCHOR
            dx,dy = mat@(b-a)
            normal=np.array([-dy,dx])/math.hypot(dx,dy)
            for f in np.linspace(.10,.90,14):
                p=a+(b-a)*f
                predicted=origin+mat@p
                offsets=np.arange(-13,14)
                xs,ys=np.rint(predicted+offsets[:,None]*normal).astype(int).T
                if min(xs)<0 or max(xs)>=w or min(ys)<0 or max(ys)>=h:
                    continue
                hits=offsets[mask[ys,xs]>0]
                if not 4<=len(hits)<=13 or hits[-1]-hits[0]+1!=len(hits) or max(abs(hits))>=13:
                    continue
                nx,ny=normal
                rows.append([nx,ny,nx*p[0]+ny*p[1],ny*p[0]-nx*p[1]])
                centers.append(normal@predicted+(hits[0]+hits[-1])/2)
        if len(rows)<16:
            return None
        design,vals=np.asarray(rows),np.asarray(centers)
        # When the HUD covers the second bend, transverse sections through
        # one junction constrain heading and translation, but barely constrain scale.
        # Keep the template scale in that direction during refinement.
        prior = np.array([[0,0,60,0],[0,0,0,60]])
        prior_values = 60*mat[:,0]
        def fit_sections(rows, values):
            return np.linalg.lstsq(np.vstack((rows, prior)),
                                   np.r_[values, prior_values], rcond=None)[0]
        fit = fit_sections(design, vals)
        keep=abs(design@fit-vals)<2.5
        if keep.sum()<16 or np.linalg.svd(design[keep,:2],compute_uv=False)[-1]<1.5:
            return None
        fit = fit_sections(design[keep], vals[keep])
        new_mat=np.array([[fit[2],-fit[3]],[fit[3],fit[2]]])
        if np.linalg.norm(fit[:2]-origin)>7 or np.linalg.norm(new_mat-mat)>.035:
            return None
        origin,mat=fit[:2],new_mat
    return origin / [w,h], mat / np.array([[w],[h]])


def screen_point(pose, point):
    origin,mat = pose
    return tuple(origin+mat@(np.array(point)-ANCHOR))


def rank_titan_sites(img, pose, sites, tried=()):
    """Prefer a clear patch under the base, in the local camera projection."""
    if not sites:
        return []
    grid = np.arange(-24, 25, 4)
    dx, dy = np.meshgrid(grid, grid)
    footprint = np.column_stack((dx.ravel(), dy.ravel()))
    footprint = footprint[(footprint**2).sum(axis=1) <= 24**2]
    origin, mat = pose
    points = np.asarray(sites)
    pixels = np.rint((origin + (points[:, None] + footprint - ANCHOR) @ mat.T) * img.size).astype(int)
    x, y = pixels.transpose(2, 0, 1)
    visible = (x >= 0) & (x < img.width) & (y >= 0) & (y < img.height)
    rgb = np.asarray(img.convert("RGB"))
    samples = rgb[y.clip(0,img.height-1), x.clip(0,img.width-1)].astype(int)
    r, g, b = samples.transpose(2, 0, 1)
    sand = (r >= 75) & (r-g >= 9) & (g-b >= 18) & (r-g < 45) & (r-b < 105)
    spread = np.percentile(g, 90, axis=1) - np.percentile(g, 10, axis=1)
    cost = 1 - (visible & sand).mean(axis=1) + np.minimum(spread/100, 1)*.35
    if len(tried):
        # Adjacent offsets often cover the very same wreck.
        distance = np.linalg.norm(points[:,None] - np.asarray(tried), axis=2).min(axis=1)
        cost += np.maximum(0, 1 - distance/52)
    # A near tie favors the earlier site in the coordinator's plan.
    order = np.argsort(np.rint(cost*12), kind="stable")
    return [sites[index] for index in order]


def perimeter_point(img, pose, center, tangent, normal):
    """Measure the outside edge in several cross-sections of the highlighted road."""
    from wastelands_team import BANK_OFFSET, EDGE_ADJUST, EDGE_GAP
    # Work in map units so clearance is independent of projection and resolution.
    offsets = np.arange(-40, 80)
    coords = (np.asarray(center) + np.arange(-8,9,4)[:,None,None]*np.asarray(tangent)
              + offsets[:,None]*np.asarray(normal))
    origin, mat = pose
    pixels = np.rint((origin+(coords-ANCHOR)@mat.T)*img.size).astype(int)
    x,y = pixels.transpose(2,0,1)
    if x.min()<0 or y.min()<0 or x.max()>=img.width or y.max()>=img.height:
        return None
    left,top = int(x.min()),int(y.min())
    crop = img.crop((left,top,int(x.max())+1,int(y.max())+1)).convert("RGB")
    r,g,b = np.asarray(crop)[y-top,x-left].astype(np.int16).transpose(2,0,1)
    red = (r>110)&(r-g>58)&(r-b>52)
    edges = []
    for row in red:
        # The boundary has a sustained red band followed by clear ground.
        for i in range(10,len(row)-EDGE_GAP-3):
            if (abs(offsets[i]+EDGE_GAP-BANK_OFFSET)<=EDGE_ADJUST and
                    row[i-10:i].sum()>=8 and row[i-1] and not row[i:i+EDGE_GAP+3].any()):
                edges.append(offsets[i])
                break
    if len(edges)<3 or np.ptp(edges)>8:
        return None
    distance = float(np.median(edges))+EDGE_GAP
    index = round(distance)-offsets[0]
    if red[:,index-2:index+3].any():
        return None
    return (np.asarray(center)+distance*np.asarray(normal)).tolist()


def map_point(pose, point):
    origin,mat = pose
    return (ANCHOR+np.linalg.solve(mat,np.array(point)-origin)).tolist()


def preview(img):
    thumb = img.copy()
    thumb.thumbnail((960,540))
    buf = io.BytesIO()
    thumb.convert("RGB").save(buf,"JPEG",quality=78)
    return base64.b64encode(buf.getvalue()).decode("ascii")


def scene(img):
    arr = np.asarray(img.convert("L").resize((80,45),Image.Resampling.BOX)).astype(float)
    return arr[12:34,4:76]


def tracked_pose(reference, pose, img):
    """Update a known map pose from terrain when all unit slots are already full."""
    if cv2 is None:
        # Reuse the pose only if textured terrain in separate quadrants is stationary.
        # On camera movement the caller can take a new measurement from the road.
        if img.size != reference.size:
            return None
        def terrain(frame):
            return np.asarray(frame.convert("L").resize((320,180), Image.Resampling.BILINEAR), dtype=np.int16)
        old, new = terrain(reference), terrain(img)
        matches = 0
        for y in (48, 92):
            for x in (40, 192):
                patch = old[y:y+36, x:x+76]
                changed = abs(new[y:y+36, x:x+76] - patch)
                if patch.std() > 8 and np.mean(changed < 5) > .92:
                    matches += 1
        return pose if matches >= 3 else None
    def features(frame):
        a=np.asarray(frame.convert("L").resize((640,360),Image.Resampling.BILINEAR))
        mask=np.zeros_like(a)
        mask[58:270,15:624]=255
        mask[58:96,260:390]=0
        mask[147:208,550:624]=0
        return cv2.ORB_create(nfeatures=850).detectAndCompute(a,mask)
    first,d1=features(reference)
    last,d2=features(img)
    if d1 is None or d2 is None or len(d2)<2:
        return None
    pairs=cv2.BFMatcher(cv2.NORM_HAMMING).knnMatch(d1,d2,k=2)
    keep=[a for a,b in pairs if a.distance<.72*b.distance]
    if len(keep)<14:
        return None
    old=np.float32([first[p.queryIdx].pt for p in keep])
    new=np.float32([last[p.trainIdx].pt for p in keep])
    warp,inliers=cv2.estimateAffinePartial2D(old,new,method=cv2.RANSAC,ransacReprojThreshold=2.)
    if warp is None or inliers.sum()<12 or inliers.mean()<.55:
        return None
    spread=np.ptp(old[inliers.ravel()>0],axis=0)
    if spread[0]<100 or spread[1]<50:
        return None
    size=np.array([640,360])
    origin,mat=pose
    return (warp[:,:2]@(origin*size)+warp[:,2])/size, (warp[:,:2]@(mat*size[:,None]))/size[:,None]


class OCR:
    """Persistent Windows OCR process. Each reply is one JSON line."""
    def __init__(self):
        self.proc = None

    def read(self, img, box=(0,0,1,1), *, zoom=2):
        if self.proc is None or self.proc.poll() is not None:
            script = Path(__file__).with_name("wastelands_ocr.ps1")
            self.proc = subprocess.Popen(["powershell.exe","-NoProfile","-NonInteractive",
                        "-ExecutionPolicy","Bypass","-File",str(script)],stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,creationflags=subprocess.CREATE_NO_WINDOW)
        l,t,r,b = [round(v*s) for v,s in zip(box,(img.width,img.height)*2)]
        part = img.crop((l,t,r,b)).convert("RGB")
        scale = min(zoom,2000/max(part.size))
        part = part.resize((round(part.width*scale),round(part.height*scale)),Image.Resampling.BICUBIC)
        buf = io.BytesIO()
        part.save(buf,"PNG")
        self.proc.stdin.write(base64.b64encode(buf.getvalue())+b"\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError("Windows OCR завершился. Проверь английский языковой пакет OCR")
        result = json.loads(line)
        if "error" in result:
            raise RuntimeError(result["error"])
        return [(word,(l+x/scale)/img.width,(t+y/scale)/img.height,
                 w/scale/img.width,h/scale/img.height) for word,x,y,w,h in result["words"]]

    def close(self):
        if self.proc is not None:
            if self.proc.poll() is None:
                self.proc.terminate()
            self.proc.wait(timeout=3)
            self.proc.stdin.close()
            self.proc.stdout.close()
            self.proc = None


def label(words, text, box=(0,0,1,1)):
    """Locate contiguous words on the same line; OCR can merge labels across columns."""
    def norm(s):
        return "".join(c for c in s.casefold() if c.isalnum() or c=="_")
    target = norm(text)
    l,t,r,b = box
    candidates = [v for v in words if l<=v[1]+v[3]/2<=r and t<=v[2]+v[4]/2<=b]
    for word,x,y,w,h in candidates:
        if not norm(word) or not target.startswith(norm(word)):
            continue
        row = sorted((v for v in candidates if v[1]>=x-.0001 and
                     abs(v[2]+v[4]/2-y-h/2)<max(h,v[4])*.52),key=lambda v:v[1])
        current = ""
        end = x
        for token,xx,yy,ww,hh in row:
            if xx-end>max(.015,h*.9):
                break
            current += norm(token)
            end = xx+ww
            if current==target:
                return ((x+end)/2,y+h/2)
            if not target.startswith(current):
                break
    return None
