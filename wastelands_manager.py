"""Read the two individual titan cards inside the Wastelands Unit Manager."""
import re
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path

import numpy as np
from PIL import Image

import twd_bot as farm
from wastelands_view import color_boxes, label


NAMES = {"amplifier":"Titan Amplifierman", "screen":"Titan Screen Man"}


@dataclass(frozen=True)
class TitanCard:
    box: tuple
    level: int | None
    button: tuple | None
    button_box: tuple | None
    price_box: tuple | None

    def upgrade_contains(self,frame,point):
        if not self.button_box:
            return False
        x,y,w,h = self.button_box
        px,py = point[0]*frame.width,point[1]*frame.height
        return x+.14*w<px<x+.58*w and y+.20*h<py<y+.80*h


def manager_bounds(img):
    rgb = np.asarray(img.convert("RGB"),dtype=np.int16)
    r,g,b = rgb.transpose(2,0,1)
    cyan = ((g>130)&(b>140)&(g-r>65)&(b-r>65)).astype(np.uint8)
    return max((box for box in color_boxes(cyan)
                if .20*img.width<box[2]<.82*img.width and box[3]>.45*img.height),
               key=lambda box:box[2]*box[3],default=None)


def _ink(image):
    pixels = np.asarray(image,dtype=np.float32)
    if pixels.ndim==3:
        pixels = pixels.min(axis=2)
    return np.clip((pixels-80)/140,0,1)


@lru_cache(maxsize=1)
def _labels():
    with Image.open(Path(__file__).with_name("wastelands_titan_labels.png")) as atlas:
        return {key:_ink(atlas.crop(box)) for key,box in (
            ("amplifier",(0,0,140,18)), ("screen",(0,18,140,36)),
            (2875,(0,36,52,57)), (3525,(52,36,104,57)), ("upgrade",(0,57,70,81)))}


def _similarity(mark,ref):
    norm = np.linalg.norm(mark)*np.linalg.norm(ref)
    if norm==0:
        return 0
    h,w = ref.shape
    padded = np.pad(mark,2)
    return max(float((padded[y:y+h,x:x+w]*ref).sum()/norm)
               for y in range(5) for x in range(5))


def _card_name(card,read):
    w = card.width
    header = card.crop((0,0,w,round(.18*w))).resize((165,30),Image.Resampling.BILINEAR)
    mark = _ink(header.crop((13,6,153,24)))
    scores = sorted(((_similarity(mark,_labels()[kind]),kind) for kind in NAMES),reverse=True)
    if scores[0][0]>.85 and scores[0][0]-scores[1][0]>.12:
        return scores[0][1]
    if read:
        header = card.crop((0,round(.025*w),w,round(.16*w)))
        words = read(header,zoom=5)
        return next((kind for kind,name in NAMES.items() if label(words,name)),None)
    return None


def _visual_level(band):
    light = np.asarray(band).min(axis=2)
    readings = []
    for threshold in (115,140,160):
        ink = light>=threshold
        runs = farm._runs(ink.any(axis=0))
        if len(runs)<4:
            continue
        (a,b),(c,d),(e,f) = runs[-3:]
        ys,xs = np.nonzero(ink[:,c:d])
        if not len(ys) or ys.max()-ys.min()<4:
            continue
        mid = (ys.min()+ys.max())/2
        if xs[ys<=mid].mean()-xs[ys>mid].mean()<.55:
            continue
        # Require the printed /8 on the same line as the numerator.
        if farm._read_green_number(ink[:,e:f],tol=.19,dollar=False)!=8:
            continue
        value = farm._read_green_number(ink[:,a:b],tol=.19,dollar=False)
        if value is not None and 0<=value<=8:
            readings.append(value)
    if len(readings)>=2 and len(set(readings))==1:
        return readings[0]
    return None


def card_level(card,read=None):
    w = card.width
    band = card.crop((round(.52*w),round(.165*w),round(.967*w),round(.258*w)))
    for sample in (band,band.resize((147,31),Image.Resampling.BICUBIC)):
        value = _visual_level(sample)
        if value is not None:
            return value
    if read:
        text = "".join(word[0] for word in read(band,zoom=6)).replace(" ","")
        hit = re.search(r"([0-8OoIl])/8$",text)
        if hit:
            return int(hit[1].translate(str.maketrans("OoIl","0011")))
    return None


def _upgrade_footer(card,read):
    w,h = card.size
    top = round(.42*w)
    rgb = np.asarray(card.crop((0,top,w,h)),dtype=np.int16)
    r,g,b = rgb.transpose(2,0,1)
    green = ((g>75)&(g-r>38)&(g-b>34)).astype(np.uint8)
    boxes = [(x,y+top,bw,bh) for x,y,bw,bh in color_boxes(green)
             if .80*w<bw<w and .11*w<bh<.26*w and abs(x+bw/2-w/2)<.05*w
             and top+y+bh<h]
    for x,y,bw,bh in sorted(boxes,key=lambda b:-b[2]*b[3]):
        name = card.crop((x+round(.17*bw),y+round(.12*bh),x+round(.60*bw),y+round(.88*bh)))
        mark = _ink(name.resize((70,24),Image.Resampling.BILINEAR))
        if _similarity(mark,_labels()["upgrade"])>.84:
            return x,y,bw,bh
        if read:
            text = "".join(word[0] for word in read(name,zoom=5)).strip().casefold()
            if text in ("upgrade","улучшить","улучшение"):
                return x,y,bw,bh
    return None


def titan_cards(frame,read=None,bounds=None):
    panel = bounds or manager_bounds(frame)
    if panel is None:
        return {}
    px,py,pw,ph = map(int,panel)
    top = py+round(.095*ph)
    bottom = py+round(.92*ph)
    region = frame.crop((px,top,px+pw,bottom)).convert("RGB")
    r,g,b = np.asarray(region,dtype=np.int16).transpose(2,0,1)
    red = ((r>140)&(r-g>85)&(r-b>75)).astype(np.uint8)
    boxes = sorted(color_boxes(red),key=lambda box:-box[2]*box[3])
    seen,found,duplicates = [],{},set()
    for x,y,w,h in boxes:
        if not (.37*pw<w<.50*pw and .55*w<h<2.6*w and y>0):
            continue
        if any(abs(x-left)<.06*w and abs(y-upper)<.06*w for left,upper in seen):
            continue
        seen.append((x,y))
        card = region.crop((x,y,x+w,y+h))
        kind = _card_name(card,read)
        if kind is None:
            continue
        if kind in found:
            duplicates.add(kind)
            continue
        left,upper = px+x,top+y
        button = button_box = price_box = None
        footer = _upgrade_footer(card,read)
        if footer:
            bx,by,bw,bh = footer
            button_box = (left+bx,upper+by,bw,bh)
            button = ((left+bx+.34*bw)/frame.width,(upper+by+.5*bh)/frame.height)
            price_box = (int(left+bx+.66*bw),int(upper+by+.17*bh),
                         int(left+bx+.985*bw),int(upper+by+.84*bh))
        found[kind] = TitanCard(tuple(map(int,(left,upper,left+w,upper+h))),
                                card_level(card,read),button,button_box,price_box)
    return {kind:card for kind,card in found.items() if kind not in duplicates}


def upgrade_price(frame,card,read=None):
    if not card.price_box:
        return None
    crop = frame.crop(card.price_box)
    mark = _ink(crop.resize((52,21),Image.Resampling.BILINEAR))
    # These two opening prices have recorded glyphs. At later levels the
    # amounts can differ by a single digit and must be read afresh.
    if card.level==0:
        scores = sorted(((_similarity(mark,_labels()[price]),price) for price in (2875,3525)),reverse=True)
        if scores[0][0]>.93 and scores[0][0]-scores[1][0]>.085:
            return scores[0][1]
    if read:
        amounts = []
        for zoom in (5,7):
            text = "".join(v[0] for v in read(crop,zoom=zoom)).replace(" ","")
            hit = re.fullmatch(r"\$(\d{1,3}(?:,\d{3})+|\d{1,7})",text)
            if not hit:
                return None
            amounts.append(int(hit[1].replace(",","")))
        if amounts[0]>0 and amounts[0]==amounts[1]:
            return amounts[0]
    return None
