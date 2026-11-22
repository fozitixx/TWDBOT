"""Screen recognition and conversion between the shared map and one RDP view."""
import base64
import io
import json
import math
from pathlib import Path
import subprocess

import cv2
import numpy as np
from PIL import Image


ANCHOR = np.array([835., 475.])


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
            template = np.zeros(tuple((hi-lo+1)[::-1]),np.uint8)
            for a,bp in np.rint(pts-lo).astype(int):
                cv2.line(template,tuple(a),tuple(bp),1,max(3,round(46*k)))
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

    def read(self, img, box=(0,0,1,1)):
        if self.proc is None or self.proc.poll() is not None:
            script = Path(__file__).with_name("wastelands_ocr.ps1")
            self.proc = subprocess.Popen(["powershell.exe","-NoProfile","-NonInteractive",
                        "-ExecutionPolicy","Bypass","-File",str(script)],stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE,stderr=subprocess.DEVNULL,creationflags=subprocess.CREATE_NO_WINDOW)
        l,t,r,b = [round(v*s) for v,s in zip(box,(img.width,img.height)*2)]
        part = img.crop((l,t,r,b)).convert("RGB")
        scale = min(2,2000/max(part.size))
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
