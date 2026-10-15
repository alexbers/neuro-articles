"""Rigorous (ball arithmetic, python-flint/arb) verification of a continuum design for the PacMan family.
Checks: (1) w0 = W(z0) lies in the open unit disk; (2) H'(w) = Phi'(w)B(w) + (Phi(w)-z0)B'(w) has no zero
in the closed unit disk (argument principle with certified arc enclosures); (3) margin m = 1/|B(w0)| (enclosure).
All inputs are exact dyadic/decimal numbers converted to exact balls."""
import sys, json
from fractions import Fraction
from flint import arb, acb, ctx
ctx.prec = 120
def A(x): return arb(str(x))
def C(re, im): return acb(A(re), A(im))
class Design:
    def __init__(s, beta, r, zr, z0, a):
        s.beta = A(beta); s.r = A(r); s.zr = zr; s.z0 = z0
        s.alist = a if isinstance(a, list) else [a]
        s.k = 1
        s.g = arb.pi()/(2*arb.pi() - 2*s.beta)
        s.eib = acb(0, s.beta).exp()
        s.tb = s.tau(zr)
    def tau(s, z):
        zz = z/s.eib
        # arg in (0, 2pi): if Im(zz) < 0 use log + 2 pi i
        lg = zz.log()
        if zz.imag < 0: lg = lg + acb(0, 2*arb.pi())
        elif not (zz.imag > 0):
            if not (zz.imag.is_zero() and zz.real < 0): raise ValueError("ambiguous branch")
        v = (s.g*lg).exp()
        xi = (1+v)/(1-v); return xi*xi
    def W(s, z):
        t = s.tau(z); return (t - s.tb)/(t - s.tb.conjugate())/s.r
    def Phi_dPhi(s, w):
        u = s.r*w
        t = (s.tb - s.tb.conjugate()*u)/(1-u)
        xi = t.sqrt()
        v = (xi-1)/(xi+1)
        lv = v.log()
        P = ((lv/s.g).exp())*s.eib
        dt = (s.tb - s.tb.conjugate())/((1-u)*(1-u))
        dv = 2/((xi+1)*(xi+1))/(2*xi)*dt
        dP = (1/s.g)*(((1/s.g - 1)*lv).exp())*dv*s.eib*s.r
        return P, dP
    def Bprod(s, w):
        B = acb(1); dB = acb(0)
        for a in s.alist:
            ac = a.conjugate(); den = 1 - ac*w
            f = (w - a)/den; df = (1 - a*ac)/(den*den)
            dB = dB*f + B*df; B = B*f
        return B, dB
    def Hp(s, w):
        # k = 1: F = (z - z0) B(W)/B(w0);  k >= 2: k-fold symmetric witness F(z) = z h(z^k),
        # h(u) = B(W(u + z0))/B(w0); in both cases F' != 0  <=>  Phi' B + k (Phi - z0) B' != 0
        P, dP = s.Phi_dPhi(w)
        B, dB = s.Bprod(w)
        return dP*B + s.k*(P - s.z0)*dB

def small_root_ball(y, L):
    """root x of (L/2)(x + 1/x) = y with |x| < 1 (the two roots have product 1); rigorous selection."""
    q = y*y - L*L
    # either square root works (the two roots are swapped); pick a formula whose branch cut is avoided
    sq = acb(0, 1)*(-q).sqrt() if q.real < 0 else q.sqrt()
    x1 = (y - sq)/L; x2 = (y + sq)/L
    if abs(x1) < 1: return x1
    if abs(x2) < 1: return x2
    raise ValueError("root selection undecided")
class DesignTS(Design):
    """two collinear slits: D0 = unit disc minus [s,1) and (-1,-s]; Phi0(w) = J^{-1}((L/2)(M(w) + 1/M(w))),
    M(w) = (w + zeta_r)/(1 + conj(zeta_r) w), J(z) = z + 1/z, L = s + 1/s."""
    def __init__(s_, sv, r, zr, z0, a):
        s_.sv = A(sv); s_.L = s_.sv + 1/s_.sv; s_.r = A(r); s_.z0 = z0
        s_.alist = a if isinstance(a, list) else [a]; s_.k = 1
        s_.zeta_r = small_root_ball(zr + 1/zr, s_.L)
    def W(s_, z):
        zt = small_root_ball(z + 1/z, s_.L); a = s_.zeta_r
        return (zt - a)/(1 - a.conjugate()*zt)/s_.r
    def Phi_dPhi(s_, w):
        u = s_.r*w; a = s_.zeta_r
        zt = (u + a)/(1 + a.conjugate()*u)
        dzt = (1 - a*a.conjugate())/((1 + a.conjugate()*u)**2)*s_.r
        y = (s_.L/2)*(zt + 1/zt); dy = (s_.L/2)*(1 - 1/(zt*zt))*dzt
        z = small_root_ball(y, acb(2))       # J^{-1}: root of z + 1/z = y inside the unit disc
        dz = dy/(1 - 1/(z*z))
        return z, dz

def verify(D, K0=4096, maxdepth=30):
    # (1) base point
    w0 = D.W(D.z0)
    ok1 = abs(w0) < 1
    Pw0, _ = D.Phi_dPhi(w0)
    ok_inv = abs(Pw0 - D.z0) < arb("1e-20")
    # (3) margin
    B0, _ = D.Bprod(w0)
    m = 1/abs(B0)
    ok_a = all(abs(a) < 1 for a in D.alist)
    # (2) winding via certified arcs
    two_pi = 2*arb.pi()
    total = arb(0); narcs = 0
    stack = [(Fraction(k, K0), Fraction(k+1, K0), 0) for k in range(K0)]
    stack.reverse()
    endvals = {}
    def pt(fr):
        if fr not in endvals:
            th = two_pi*arb(fr.numerator)/arb(fr.denominator)
            endvals[fr] = D.Hp(acb(th.cos(), th.sin()))
        return endvals[fr]
    while stack:
        lo, hi, dep = stack.pop()
        thm = two_pi*(arb(lo.numerator)/arb(lo.denominator) + arb(hi.numerator)/arb(hi.denominator))/2
        half = two_pi*(arb(hi.numerator)/arb(hi.denominator) - arb(lo.numerator)/arb(lo.denominator))/2
        # ball containing the arc: center e^{i thm}, radius half (chord <= arc length)
        cen = acb(thm.cos(), thm.sin())
        # box containing the whole arc: |e^{i t} - e^{i thm}| <= |t - thm| <= half (+ rounding of cen)
        R = half.upper() + cen.real.rad() + cen.imag.rad()
        wball = acb(arb(cen.real.mid(), R), arb(cen.imag.mid(), R))
        try:
            val = D.Hp(wball); bad = val.contains(0) or not (abs(val) > 0)
        except ValueError:
            bad = True
        if bad:
            if dep >= maxdepth: return dict(ok=False, reason="arc not certified", lo=float(lo), hi=float(hi))
            mid = (lo+hi)/2
            stack.append((mid, hi, dep+1)); stack.append((lo, mid, dep+1)); continue
        e0 = pt(lo); e1 = pt(hi)
        total += (e1/e0).arg(); narcs += 1
    wind = total/two_pi
    return dict(k=D.k, ok_base=bool(ok1), ok_inverse=bool(ok_inv), ok_zeros_in_disk=bool(ok_a), w0=str(w0), margin=str(m), winding=str(wind), narcs=narcs,
                ok_winding=bool(abs(wind) < 0.5))
if __name__ == "__main__":
    p = json.load(open(sys.argv[1]))
    al = p["a"]
    al = [C(*q) for q in al] if isinstance(al[0], list) else C(*al)
    if p.get("family", "pac") == "ts":
        D = DesignTS(p["s"], p["r"], C(*p["zr"]), C(*p["z0"]), al)
    else:
        D = Design(p["beta"], p["r"], C(*p["zr"]), C(*p["z0"]), al)
    D.k = int(p.get("k", 1))
    res = verify(D, int(p.get("K0", 4096)))
    print(json.dumps(res, indent=1))
