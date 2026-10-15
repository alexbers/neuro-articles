import numpy as np
from numpy.polynomial import polynomial as P
# Phi(w) = k(u), u = r (w + c)/(1 + conj(c) w), k(u) = u/(1-u)^2 ; base point z0 = Phi(w0); Blaschke zero a.
def Ppoly(r, c, w0, a):
    cb = np.conj(c); ab = np.conj(a)
    E = np.array([1 - r*c, cb - r])            # E(w) = (1 + cb w) - r (w + c)
    S = np.array([1 + r*c, cb + r])            # (1 + cb w) + r (w + c)
    wa = np.array([-a, 1.0]); oa = np.array([1.0, -ab])
    wc = np.array([c, 1.0]); oc = np.array([1.0, cb])
    u0 = r*(w0 + c)/(1 + cb*w0); z0 = u0/(1-u0)**2
    t1 = r*(1-abs(c)**2)*P.polymul(P.polymul(S, wa), oa)
    E3 = P.polymul(P.polymul(E, E), E)
    t2 = (1-abs(a)**2)*P.polysub(r*P.polymul(P.polymul(wc, oc), E), z0*E3)
    return P.polyadd(t1, t2), z0
def margin(w0, a): return abs(1 - np.conj(a)*w0)/abs(w0 - a)
def feasible(r, c, w0, a):
    if not (0 < r < 1 and abs(c) < 1 and abs(w0) < 1 and abs(a) < 1): return None
    p, z0 = Ppoly(r, c, w0, a)
    rts = P.polyroots(p)
    return np.abs(rts).min()
if __name__ == "__main__":
    # sanity: compare with direct numerical derivative
    r, c, w0, a = 0.9, 0.1+0.2j, 0.3-0.1j, 0.5+0.5j
    p, z0 = Ppoly(r, c, w0, a)
    def Phi(w): u = r*(w+c)/(1+np.conj(c)*w); return u/(1-u)**2
    w = 0.2+0.3j; h = 1e-6
    dPhi = (Phi(w+h)-Phi(w-h))/(2*h)
    B = (w-a)/(1-np.conj(a)*w); dB = (1-abs(a)**2)/(1-np.conj(a)*w)**2
    Hp = dPhi*B + (Phi(w)-z0)*dB
    E = (1+np.conj(c)*w) - r*(w+c)
    print(Hp*(1-np.conj(a)*w)**2*E**3, P.polyval(w, p))

def kinv(z):
    s = np.sqrt((2*z+1)**2 - 4*z*z + 0j)
    u1 = ((2*z+1) - s)/(2*z); u2 = ((2*z+1) + s)/(2*z)
    return u1 if abs(u1) < abs(u2) else u2
def Phi(w, r, c): u = r*(w+c)/(1+np.conj(c)*w); return u/(1-u)**2
def dPhi(w, r, c, h=1e-7): return (Phi(w+h, r, c) - Phi(w-h, r, c))/(2*h)
def Winv(z, r, c):
    u = kinv(z)/r
    return (u - c)/(1 - np.conj(c)*u)
