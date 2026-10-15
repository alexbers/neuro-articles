import mpmath as mp, json, sys
mp.mp.dps = 40
p = json.load(open(sys.argv[1]))
g = mp.mpf
s = g(p['s']); L = s + 1/s; r = g(p['r']); zr = mp.mpc(g(p['zr'][0]), g(p['zr'][1]))
z0 = mp.mpc(g(p['z0'][0]), g(p['z0'][1])); a = mp.mpc(g(p['a'][0][0]), g(p['a'][0][1]))
def small(y, LL):
    q = mp.sqrt(y*y - LL*LL); x1 = (y-q)/LL; x2 = (y+q)/LL
    return x1 if abs(x1) < abs(x2) else x2
zeta_r = small(zr + 1/zr, L)
def Phi(w):
    u = r*w; zt = (u + zeta_r)/(1 + mp.conj(zeta_r)*u); y = (L/2)*(zt + 1/zt)
    return small(y, 2)
def Hp(w):
    P = Phi(w); dP = mp.diff(Phi, w); den = 1 - mp.conj(a)*w
    return dP*(w-a)/den + (P - z0)*(1-abs(a)**2)/den**2
# locate approximate position of minimal |H'| on the circle
best = None
for k in range(4000):
    th = 2*mp.pi*k/4000; v = abs(Hp(mp.expj(th)))
    if best is None or v < best[0]: best = (v, th)
th = best[1]; roots = []
for dth in [-0.01, -0.003, 0, 0.003, 0.01]:
    for rad in ['0.995', '1.0', '1.005']:
        try:
            f = (lambda w: Hp(w)/(w-roots[0])) if roots else Hp
            z = mp.findroot(f, mp.mpf(rad)*mp.expj(th+dth))
            if abs(abs(z)-1) < 0.1 and all(abs(z-q) > 1e-20 for q in roots): roots.append(z)
        except Exception: pass
        if len(roots) >= 2: break
    if len(roots) >= 2: break
print("min|H'| on circle ~", mp.nstr(best[0], 5), "at", mp.nstr(th, 8))
print("zeros near circle:", [(mp.nstr(abs(z), 15), mp.nstr(mp.arg(z), 10)) for z in roots])
