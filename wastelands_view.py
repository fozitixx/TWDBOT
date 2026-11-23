"""Screen recognition and conversion between the shared map and one RDP view."""
import base64
import io
import json
import math
from pathlib import Path
import subprocess

import numpy as np
from PIL import Image, ImageDraw

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
        fit,_,rank,_=np.linalg.lstsq(design,vals,rcond=None)
        keep=abs(design@fit-vals)<2.5
        if rank<4 or keep.sum()<16:
            return None
        fit,_,rank,_=np.linalg.lstsq(design[keep],vals[keep],rcond=None)
        new_mat=np.array([[fit[2],-fit[3]],[fit[3],fit[2]]])
        if rank<4 or np.linalg.norm(fit[:2]-origin)>7 or np.linalg.norm(new_mat-mat)>.035:
            return None
        origin,mat=fit[:2],new_mat
    return origin / [w,h], mat / np.array([[w],[h]])


def screen_point(pose, point):
    origin,mat = pose
    return tuple(origin+mat@(np.array(point)-ANCHOR))


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
