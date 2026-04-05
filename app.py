"""
╔══════════════════════════════════════════════════════════╗
║   Lectra Pattern Converter  v1.4                         ║
║   AAMA/ASTM DXF + RUL  — Perfect Curves with ezdxf.path ║
║   High-precision curve rendering (Lectra-quality)       ║
╚══════════════════════════════════════════════════════════╝
"""
VERSION = "v2.0"
import tkinter as tk
from tkinter import filedialog, messagebox
import customtkinter as ctk
import os, threading, math, struct, re
from reportlab.pdfgen import canvas as pdf_canvas
from reportlab.lib.units import cm
import ezdxf
from ezdxf import recover as dxf_recover
from ezdxf.path import make_path
from PIL import Image, ImageDraw, ImageTk

# ═══════════════════════════════════════════════
ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")
BG_DARK  =  "#0A0A0A "
BG_PANEL =  "#111111 "
BG_CARD  =  "#1A1A1A "
ACCENT   =  "#F07800 "
ACCENT2  =  "#FF9500 "
ERR      =  "#FF4444 "
TEXT_SEC =  "#888888 "
BORDER   =  "#2A2A2A "
LAYER_COLORS = {
    "1":  (255, 255, 255),
    "14": (100, 220, 100),
    "8":  (255, 200,  60),
    "4":  (255, 120, 120),
    "7":  ( 50,  50,  80),
    "2":  (160, 200, 255),
    "13": (200, 150, 255),
}
DEFAULT_COLOR = (79, 142, 247)
GRADE_COLORS = [
    (255,  80,  80),   # XXS
    (255, 165,  40),   # XS
    (230, 230,  50),   # S
    (255, 255, 255),   # M  (base)
    ( 80, 210,  80),   # L
    ( 60, 160, 255),   # XL
    (200,  80, 255),   # XXL
]

# ═══════════════════════════════════════════════
# RUL PARSER
# ═══════════════════════════════════════════════
class RULParser:
    def __init__(self):
        self.sizes      = []
        self.sample     = "M"
        self.sample_idx = 3
        self.rules      = {}

    def parse(self, filepath: str):
        with open(filepath,  "rb ") as f:
            raw = f.read()
        text = raw.decode( "latin-1 ", errors= "replace ")

        m = re.search(r "SIZE LIST:\s*(.+) ", text)
        if m: self.sizes = m.group(1).strip().split()
        m = re.search(r "SAMPLE SIZE:\s*(\S+) ", text)
        if m: self.sample = m.group(1).strip()
        if self.sample in self.sizes:
            self.sample_idx = self.sizes.index(self.sample)

        blocks = re.split(r "RULE:\s*DELTA\s+(\d+) ", text)
        i = 1
        while i  < len(blocks) - 1:
            rnum = int(blocks[i])
            pairs = re.findall(r "(-?\d+\.?\d*),\s*(-?\d+\.?\d*) ", blocks[i+1])
            if pairs:
                self.rules[rnum] = [(float(x), float(y)) for x, y in pairs]
            i += 2

    def get_delta_mm(self, rule_num: int, size_idx: int):
        if rule_num in self.rules and size_idx  < len(self.rules[rule_num]):
            return self.rules[rule_num][size_idx]
        return (0.0, 0.0)

# ═══════════════════════════════════════════════
# GRADING ENGINE
# ═══════════════════════════════════════════════
def _arc_length(pts, i1, i2):
    total = 0.0
    for k in range(i1, i2):
        dx = pts[k+1][0] - pts[k][0]
        dy = pts[k+1][1] - pts[k][1]
        total += math.hypot(dx, dy)
    return total

def _arc_length_wrap(pts, i1, i2):
    n = len(pts) - 1
    if i2 >= i1:
        return _arc_length(pts, i1, i2)
    else:
        return (_arc_length(pts, i1, n) + _arc_length(pts, 0, i2))

def compute_graded_poly(base_pts, grade_indices, rul, size_idx):
    n = len(base_pts) - 1
    n_grades = len(grade_indices)
    
    if n_grades == 0:
        return list(base_pts)
    
    grade_deltas = {}
    for gi, rule in grade_indices:
        dx_mm, dy_mm = rul.get_delta_mm(rule, size_idx)
        grade_deltas[gi] = (dx_mm * 0.1, dy_mm * 0.1)
    
    graded = []
    for pi in range(len(base_pts)):
        pt = base_pts[pi]
        pi_mod = pi % n
        
        if pi_mod in grade_deltas:
            dx, dy = grade_deltas[pi_mod]
            graded.append((pt[0] + dx, pt[1] + dy))
            continue
        
        prev_gi = None
        next_gi = None
        for gi, rule in grade_indices:
            if gi <= pi_mod:
                prev_gi = gi
        for gi, rule in grade_indices:
            if gi >= pi_mod:
                next_gi = gi
                break
        
        if prev_gi is None:
            prev_gi = grade_indices[-1][0]
        if next_gi is None:
            next_gi = grade_indices[0][0]
        
        dx_a, dy_a = grade_deltas[prev_gi]
        dx_b, dy_b = grade_deltas[next_gi]
        
        if prev_gi == next_gi:
            t = 0.0
        elif prev_gi <= pi_mod and pi_mod <= next_gi:
            len_ap = _arc_length(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-9 else 0.0
        else:
            len_ap = _arc_length_wrap(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length_wrap(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-9 else 0.0
        
        t = max(0.0, min(1.0, t))
        dx = dx_a + t * (dx_b - dx_a)
        dy = dy_a + t * (dy_b - dy_a)
        graded.append((pt[0] + dx, pt[1] + dy))
    
    return graded

# ═══════════════════════════════════════════════
# DXF PARSER - WITH ezdxf.path FOR PERFECT CURVES
# ═══════════════════════════════════════════════
class AAMAParser:
    def __init__(self):
        self.entities     = []
        self.bounds       = None
        self.unit_name    = "mm→cm"
        self.scale        = 0.1
        self.metadata     = {}
        self.grade_indices= []
        self.rul_parser   = None
        self.graded_polys = {}
        self._base_cut_polys = []

    def parse(self, filepath: str):
        self.entities = []; self.metadata = {}
        self.grade_indices = []; self.graded_polys = {}
        self._base_cut_polys = []

        try:
            doc,  _ = dxf_recover.readfile(filepath)
        except Exception as e:
            raise RuntimeError(f "DXF পড়তে পারছি না:\n{e} ")

        try:
            ins = doc.header.get( "$INSUNITS ", None)
        except Exception:
            ins = None

        msp = doc.modelspace()
        for ent in msp:
            if ent.dxftype() ==  "TEXT ":
                try: self._parse_meta(ent.dxf.text.strip())
                except: pass
            elif ent.dxftype() ==  "INSERT ":
                block = doc.blocks.get(ent.dxf.name)
                if block: self._parse_block(block, ins)

        if not self.entities:
            self._parse_entities(msp, ins)

        self._update_bounds()

    def _parse_block(self, block, ins_hint):
        raw_xs = []
        for ent in block:
            if ent.dxftype() ==  "POLYLINE ":
                for v in ent.vertices: raw_xs.append(v.dxf.location.x)
            elif ent.dxftype() ==  "LINE ":
                raw_xs += [ent.dxf.start.x, ent.dxf.end.x]
        if not raw_xs: return

        rw = max(raw_xs) - min(raw_xs)
        sc = 0.1 if (ins_hint != 5 and rw  > 20) else 1.0
        self.scale = sc

        point_rules = {}
        for ent in block:
            if ent.dxftype() ==  "TEXT ":
                txt = ent.dxf.text.strip()
                m = re.match(r "^#\s*(\d+)$ ", txt)
                if m and str(ent.dxf.layer) ==  "1 ":
                    pos = ent.dxf.insert
                    key = (round(pos.x*sc, 6), round(pos.y*sc, 6))  # 6 decimal precision
                    point_rules[key] = int(m.group(1))

        for ent in block:
            t   = ent.dxftype()
            lay = str(getattr(ent.dxf,  "layer ",  "1 "))

            if t ==  "POLYLINE ":
                verts = list(ent.vertices)
                pts   = [(round(v.dxf.location.x*sc, 6), round(v.dxf.location.y*sc, 6))
                         for v in verts]
                if ent.is_closed and pts  and pts[0] != pts[-1]:
                    pts.append(pts[0])

                if pts:
                    self._add( "POLYLINE ", pts, lay)
                    if lay ==  "1 ":
                        self._base_cut_polys.append(pts)
                        gi = []
                        for vi, pt in enumerate(pts[:-1]):
                            key = (round(pt[0], 6), round(pt[1], 6))
                            if key in point_rules:
                                gi.append((vi, point_rules[key]))
                        if gi and not self.grade_indices:
                            self.grade_indices = gi

            elif t ==  "LWPOLYLINE ":
                # FIXED: Use ezdxf.path for perfect curve handling with bulge
                try:
                    path = make_path(ent)
                    pts = [(round(p[0]*sc, 6), round(p[1]*sc, 6)) 
                           for p in path.flattening(distance=0.005)]  # High precision
                    if pts:
                        self._add( "LWPOLYLINE ", pts, lay)
                        if lay ==  "1 " and not self._base_cut_polys:
                            self._base_cut_polys.append(pts)
                except:
                    # Fallback to old method
                    pts = [(round(p[0]*sc, 6), round(p[1]*sc, 6)) for p in ent.get_points()]
                    if ent.closed and pts and pts[0] != pts[-1]:
                        pts.append(pts[0])
                    if pts:
                        self._add( "LWPOLYLINE ", pts, lay)
                        if lay ==  "1 " and not self._base_cut_polys:
                            self._base_cut_polys.append(pts)

            elif t ==  "SPLINE ":
                # FIXED: Use ezdxf.path for smooth spline curves
                try:
                    path = make_path(ent)
                    pts = [(round(p[0]*sc, 6), round(p[1]*sc, 6)) 
                           for p in path.flattening(distance=0.005)]  # High precision
                    if pts: self._add( "SPLINE ", pts, lay)
                except: pass

            elif t ==  "LINE ":
                s, e = ent.dxf.start, ent.dxf.end
                self._add( "LINE ", [(round(s.x*sc, 6),round(s.y*sc, 6)),
                                     (round(e.x*sc, 6),round(e.y*sc, 6))], lay)

            elif t ==  "ARC ":
                # FIXED: Use ezdxf.path for accurate arc
                try:
                    path = make_path(ent)
                    pts = [(round(p[0]*sc, 6), round(p[1]*sc, 6)) 
                           for p in path.flattening(distance=0.005)]
                    if pts: self._add( "ARC ", pts, lay)
                except:
                    # Fallback
                    pts = self._arc_pts(ent, sc)
                    if pts: self._add( "ARC ", pts, lay)

            elif t ==  "CIRCLE ":
                # FIXED: Use ezdxf.path for perfect circle
                try:
                    path = make_path(ent)
                    pts = [(round(p[0]*sc, 6), round(p[1]*sc, 6)) 
                           for p in path.flattening(distance=0.005)]
                    self._add( "CIRCLE ", pts, lay)
                except:
                    # Fallback
                    cx,cy = ent.dxf.center.x*sc, ent.dxf.center.y*sc
                    r = ent.dxf.radius*sc
                    self._add( "CIRCLE ", self._circle_pts(cx,cy,r), lay)

            elif t in ( "TEXT ", "MTEXT "):
                try:
                    pos = ent.dxf.insert
                    txt = ent.dxf.text if t== "TEXT " else ent.plain_mtext()
                    txt = txt.strip()
                    px, py = pos.x*sc, pos.y*sc
                    if txt and not re.match(r "^#\s*\d+$ ", txt):
                        h = max(getattr(ent.dxf, "height ",3)*sc, 0.2)
                        self.entities.append({
                             "type ": "TEXT ", "points ":[(round(px, 6),round(py, 6))],
                             "text ":txt, "height ":h, "layer ":lay,
                             "color ":LAYER_COLORS.get(lay,DEFAULT_COLOR)})
                        self._parse_meta(txt)
                except: pass

            elif t ==  "INSERT ":
                try:
                    for sub in ent.virtual_entities():
                        sl = str(getattr(sub.dxf, "layer ", "1 "))
                        st = sub.dxftype()
                        if st ==  "LINE ":
                            s2,e2 = sub.dxf.start, sub.dxf.end
                            self._add( "LINE ",[(round(s2.x*sc, 6),round(s2.y*sc, 6)),
                                               (round(e2.x*sc, 6),round(e2.y*sc, 6))],sl)
                        elif st ==  "LWPOLYLINE ":
                            try:
                                path = make_path(sub)
                                pts=[(round(p[0]*sc, 6),round(p[1]*sc, 6)) 
                                     for p in path.flattening(distance=0.005)]
                                if pts: self._add( "LWPOLYLINE ",pts,sl)
                            except:
                                pts=[(round(p[0]*sc, 6),round(p[1]*sc, 6)) for p in sub.get_points()]
                                if pts: self._add( "LWPOLYLINE ",pts,sl)
                except: pass

    def _parse_entities(self, container, ins_hint):
        raw_xs = []
        for ent in container:
            if ent.dxftype()== "LWPOLYLINE ":
                for p in ent.get_points(): raw_xs.append(p[0])
        sc = 0.1 if (raw_xs and max(raw_xs) >20) else 1.0
        self.scale = sc
        for ent in container:
            t   = ent.dxftype()
            lay = str(getattr(ent.dxf, "layer ", "1 "))
            if t== "LINE ":
                s,e=ent.dxf.start,ent.dxf.end
                self._add( "LINE ",[(round(s.x*sc, 6),round(s.y*sc, 6)),
                                    (round(e.x*sc, 6),round(e.y*sc, 6))],lay)
            elif t== "LWPOLYLINE ":
                try:
                    path = make_path(ent)
                    pts=[(round(p[0]*sc, 6),round(p[1]*sc, 6)) 
                         for p in path.flattening(distance=0.005)]
                    if pts: self._add( "LWPOLYLINE ",pts,lay)
                except:
                    pts=[(round(p[0]*sc, 6),round(p[1]*sc, 6)) for p in ent.get_points()]
                    if ent.closed and pts and pts[0]!=pts[-1]: pts.append(pts[0])
                    if pts: self._add( "LWPOLYLINE ",pts,lay)

    def attach_rul(self, rul):
        self.rul_parser   = rul
        self.graded_polys = {}

        if not self._base_cut_polys or not rul.sizes:
            return

        for size_idx, size_name in enumerate(rul.sizes):
            graded_polys_for_size = []
            for base_poly in self._base_cut_polys:
                gp = compute_graded_poly(
                    base_poly, self.grade_indices, rul, size_idx)
                graded_polys_for_size.append(gp)
            self.graded_polys[size_name] = graded_polys_for_size

        self._update_bounds(include_graded=True)

    def _update_bounds(self, include_graded=False):
        xs, ys = [], []
        for e in self.entities:
            for p in e[ "points "]: xs.append(p[0]); ys.append(p[1])
        if include_graded:
            for polys in self.graded_polys.values():
                for poly in polys:
                    for p in poly: xs.append(p[0]); ys.append(p[1])
        if xs: self.bounds = (min(xs),min(ys),max(xs),max(ys))

    def _add(self, etype, pts, layer):
        self.entities.append({
             "type ":etype, "points ":pts, "layer ":layer,
             "color ":LAYER_COLORS.get(layer,DEFAULT_COLOR)})

    def _parse_meta(self, txt):
        for label, key in [
            ( "Style Name ", "style "),( "Piece Name ", "piece "),
            ( "Sample Size ", "size "),( "Size ", "size "),
            ( "Grade Rule Table ", "grade "),( "Author ", "author "),
            ( "Creation Date ", "date "),( "Units ", "units "),
            ( "Annotation ", "annotation "),( "Quantity ", "quantity "),
        ]:
            if txt.startswith(label+ ": "):
                v=txt.split( ": ",1)[1].strip()
                if v: self.metadata[key]=v

    def _arc_pts(self, arc, sc, steps=128):
        try:
            cx,cy=arc.dxf.center.x*sc, arc.dxf.center.y*sc
            r=arc.dxf.radius*sc
            sa=math.radians(arc.dxf.start_angle)
            ea=math.radians(arc.dxf.end_angle)
            if ea <sa: ea+=2*math.pi
            return [(round(cx+r*math.cos(sa+(ea-sa)*i/steps), 6),
                     round(cy+r*math.sin(sa+(ea-sa)*i/steps), 6))
                    for i in range(steps+1)]
        except: return []

    def _circle_pts(self, cx, cy, r, steps=256):
        return [(round(cx+r*math.cos(2*math.pi*i/steps), 6),
                 round(cy+r*math.sin(2*math.pi*i/steps), 6))
                for i in range(steps+1)]

# ═══════════════════════════════════════════════
# PREVIEW RENDERER (Same as before)
# ═══════════════════════════════════════════════
class PreviewRenderer:
    BG       = (13, 15, 20)
    GRID_MAJ = (35, 42, 65)
    GRID_MIN = (20, 26, 44)
    RULER_BG = (18, 22, 38)
    RULER_FG = (110, 140, 200)

    def render(self, parser, cw, ch, zoom=1.0, pan_x=0.0, pan_y=0.0):
        img  = Image.new( "RGB ", (cw, ch), self.BG)
        draw = ImageDraw.Draw(img)

        if not parser.entities or not parser.bounds:
            draw.text((cw//2-130, ch//2),  "Preview খালি ", fill=(120,140,180))
            return img

        b  = parser.bounds
        dw = (b[2]-b[0]) or 1
        dh = (b[3]-b[1]) or 1

        RULER = 38
        aw = cw-RULER; ah = ch-RULER
        base  = min(aw/dw, ah/dh) * 0.88
        scale = base * zoom

        cx  = RULER + aw/2 + pan_x
        cy  = RULER + ah/2 + pan_y
        mxc = (b[0]+b[2])/2; myc = (b[1]+b[3])/2

        def tx(x): return cx + (x-mxc)*scale
        def ty(y): return cy - (y-myc)*scale

        for step, col in [(1,self.GRID_MIN),(10,self.GRID_MAJ)]:
            gx=math.floor(b[0]/step)*step
            while gx <=b[2]+step:
                sx=int(tx(gx))
                if RULER <=sx <=cw: draw.line([(sx,RULER),(sx,ch)],fill=col,width=1)
                gx+=step
            gy=math.floor(b[1]/step)*step
            while gy <=b[3]+step:
                sy=int(ty(gy))
                if RULER <=sy <=ch: draw.line([(RULER,sy),(cw,sy)],fill=col,width=1)
                gy+=step

        if parser.graded_polys and parser.rul_parser:
            sizes  =  parser.rul_parser.sizes
            sample = parser.rul_parser.sample
            for si, sname in enumerate(sizes):
                if sname == sample: continue
                polys = parser.graded_polys.get(sname, [])
                col   = GRADE_COLORS[si % len(GRADE_COLORS)]
                for poly_pts in polys:
                    if len(poly_pts)  < 2: continue
                    sc2 = [(int(tx(p[0])),int(ty(p[1]))) for p in poly_pts]
                    for i in range(len(sc2)-1):
                        x1,y1=sc2[i]; x2,y2=sc2[i+1]
                        if max(x1,x2) >=RULER and min(x1,x2) <=cw and \
                           max(y1,y2) >=RULER and min(y1,y2) <=ch:
                            draw.line([(x1,y1),(x2,y2)],fill=col,width=1)

        order = [ "7 ", "2 ", "13 ", "14 ", "8 ", "4 ", "1 "]
        by_lay = {}
        for e in parser.entities: by_lay.setdefault(e.get( "layer ", "1 "),[]).append(e)
        draw_order = []
        for l in order: draw_order.extend(by_lay.get(l,[]))
        for l,es in by_lay.items():
            if l not in order: draw_order.extend(es)

        for ent in draw_order:
            pts   = ent[ "points "]
            etype = ent[ "type "]
            col   = ent.get( "color ",DEFAULT_COLOR)
            lay   = ent.get( "layer ", "1 ")

            if etype== "TEXT ":
                if pts:
                    sx,sy=int(tx(pts[0][0])),int(ty(pts[0][1]))
                    if RULER <=sx <=cw and RULER <=sy <=ch:
                        draw.text((sx,sy),ent.get( "text ", " ")[:40],fill=col)
                continue
            if len(pts) <2: continue
            lw=2 if lay== "1 " else 1
            sc2=[(int(tx(p[0])),int(ty(p[1]))) for p in pts]
            for i in range(len(sc2)-1):
                x1,y1=sc2[i]; x2,y2=sc2[i+1]
                if max(x1,x2) >=RULER and min(x1,x2) <=cw and \
                   max(y1,y2) >=RULER and min(y1,y2) <=ch:
                    draw.line([(x1,y1),(x2,y2)],fill=col,width=lw)

        draw.rectangle([0,0,cw,RULER],fill=self.RULER_BG)
        draw.rectangle([0,0,RULER,ch],fill=self.RULER_BG)
        draw.line([(RULER,RULER),(cw,RULER)],fill=(40,50,80),width=1)
        draw.line([(RULER,RULER),(RULER,ch)],fill=(40,50,80),width=1)

        rstep=10
        gx2=math.floor(b[0]/rstep)*rstep
        while gx2 <=b[2]+rstep:
            sx=int(tx(gx2))
            if RULER+2 <=sx <=cw-2:
                draw.line([(sx,RULER-8),(sx,RULER)],fill=self.RULER_FG,width=1)
                draw.text((sx-8,RULER-20),f "{int(gx2)} ",fill=self.RULER_FG)
            gx2+=rstep
        gy2=math.floor(b[1]/rstep)*rstep
        while gy2 <=b[3]+rstep:
            sy=int(ty(gy2))
            if RULER+2 <=sy <=ch-2:
                draw.line([(RULER-8,sy),(RULER,sy)],fill=self.RULER_FG,width=1)
                draw.text((2,sy-6),f "{int(gy2)} ",fill=self.RULER_FG)
            gy2+=rstep

        w_cm=round(dw,1); h_cm=round(dh,1)
        n_sz=len(parser.graded_polys) if parser.graded_polys else 1
        draw.text((RULER+6,10),
                   f "  {w_cm}×{h_cm}cm  zoom{zoom:.1f}×  {parser.unit_name}  sizes:{n_sz} ",
                  fill=self.RULER_FG)

        if parser.graded_polys and parser.rul_parser:
            sizes=parser.rul_parser.sizes; sample=parser.rul_parser.sample
            lx=cw-78
            draw.text((lx,6), "Sizes: ",fill=self.RULER_FG)
            for si,sn in enumerate(sizes):
                col=GRADE_COLORS[si%len(GRADE_COLORS)]
                ly=18+si*13
                draw.rectangle([lx,ly,lx+10,ly+9],fill=col)
                draw.text((lx+14,ly),f "{'►' if sn==sample else ' '}{sn} ",fill=col)
        else:
            for i,(l,lb) in enumerate([( "1 ", "Cut "),( "14 ", "Sew "),
                                        ( "8 ", "Grain "),( "4 ", "Notch ")]):
                col=LAYER_COLORS.get(l,DEFAULT_COLOR)
                lx=cw-110; ly=8+i*14
                draw.rectangle([lx,ly,lx+12,ly+10],fill=col)
                draw.text((lx+16,ly),lb,fill=self.RULER_FG)

        return img

# ═══════════════════════════════════════════════
# PDF/AI/SVG EXPORTERS (Same as before - keep your existing code)
# ═══════════════════════════════════════════════
# ... [Keep all your existing exporter classes unchanged] ...

# Main App class (same as your desktop app)
class LectraApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(f "Flaremo DXF to Ai Converter  ·  {VERSION} ")
        self.geometry( "1250x760 "); self.minsize(980,640)
        self.configure(fg_color=BG_DARK)
        self.parser=None; self.filepath=None; self._tk_img=None
        self._zoom=1.0; self._pan_x=0.0; self._pan_y=0.0; self._drag_st=None
        self._logo_img = None
        try:
            from PIL import Image, ImageTk
            import os
            logo_path = os.path.join(os.path.dirname(__file__), "flaremo_logo.png")
            img = Image.open(logo_path).resize((48, 48), Image.LANCZOS)
            self._logo_img = ImageTk.PhotoImage(img)
        except Exception:
            pass
        self._build_ui()

    def _build_ui(self):
        # ... [Keep your existing UI code] ...
        pass

    # ... [Keep all your existing methods] ...

if __name__== "__main__ ":
    app=LectraApp(); app.mainloop()
