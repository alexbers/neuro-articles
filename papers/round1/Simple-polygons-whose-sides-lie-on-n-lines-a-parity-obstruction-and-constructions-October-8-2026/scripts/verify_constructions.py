# Run from the paper directory:  python3 scripts/verify_constructions.py
# Independent exact-arithmetic re-verification of the four certified polygons.
import json, re, itertools
from fractions import Fraction as F

def inter(l1, l2):
    a1,b1,c1 = l1; a2,b2,c2 = l2
    det = a1*b2 - a2*b1
    if det == 0: return None
    return (F(c1*b2 - c2*b1, det), F(a1*c2 - a2*c1, det))

def orient(p,q,r):
    return (q[0]-p[0])*(r[1]-p[1]) - (q[1]-p[1])*(r[0]-p[0])

def on_seg(p,q,r):  # r on closed segment pq, given collinear
    return min(p[0],q[0])<=r[0]<=max(p[0],q[0]) and min(p[1],q[1])<=r[1]<=max(p[1],q[1])

def seg_inter(a,b,c,d):
    d1=orient(c,d,a); d2=orient(c,d,b); d3=orient(a,b,c); d4=orient(a,b,d)
    if ((d1>0 and d2<0) or (d1<0 and d2>0)) and ((d3>0 and d4<0) or (d3<0 and d4>0)): return True
    if d1==0 and on_seg(c,d,a): return True
    if d2==0 and on_seg(c,d,b): return True
    if d3==0 and on_seg(a,b,c): return True
    if d4==0 and on_seg(a,b,d): return True
    return False

def parse_lean_poly(src, name):
    m = re.search(r'def %s : List Pt := \[(.*?)\]' % name, src, re.S)
    pts = re.findall(r'⟨\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)\s*⟩', m.group(1))
    return [(F(int(x),int(w)), F(int(y),int(w))) for x,y,w in pts]

def parse_lean_lines(src, name):
    m = re.search(r'def %s : List Ln := \[(.*?)\]' % name, src, re.S)
    return [tuple(int(v) for v in t) for t in re.findall(r'⟨\s*(-?\d+),\s*(-?\d+),\s*(-?\d+)\s*⟩', m.group(1))]

lean = open('lean/Main.lean').read()
for n in (7,9,11,13):
    d = json.load(open(f'data/poly{n}.json'))
    lines = [tuple(l) for l in d['lines']]
    cyc = [tuple(c) for c in d['cycle']]
    assert len(lines)==n
    assert lines == parse_lean_lines(lean, f'lines{n}'), f'lines{n} mismatch lean/json'
    # general position
    for i,j in itertools.combinations(range(n),2):
        assert inter(lines[i],lines[j]) is not None, 'parallel'
    pts = {}
    for i,j in itertools.combinations(range(n),2):
        pts[(i,j)] = inter(lines[i],lines[j])
    allp = list(pts.values())
    assert len(set(allp)) == len(allp), 'three concurrent'
    # polygon
    k = len(cyc)
    V = [pts[tuple(sorted(c))] for c in cyc]
    leanV = parse_lean_poly(lean, f'poly{n}')
    assert V == leanV, f'poly{n} vertices differ from lean'
    assert len(set(cyc)) == k
    # consecutive share a line
    side_line = []
    for t in range(k):
        s = set(cyc[t]) & set(cyc[(t+1)%k])
        assert len(s)==1, (n,t,cyc[t],cyc[(t+1)%k])
        side_line.append(s.pop())
    # non-collinear consecutive triples
    for t in range(k):
        assert orient(V[t-1],V[t],V[(t+1)%k]) != 0
    # non-adjacent sides disjoint
    for i in range(k):
        for j in range(i+2,k):
            if j+2 <= k+i:
                assert not seg_inter(V[i],V[(i+1)%k],V[j],V[(j+1)%k]), (n,i,j)
    # edge set as pairs of line pairs
    used_pairs = set(tuple(sorted(c)) for c in cyc)
    missing = set(itertools.combinations(range(n),2)) - used_pairs
    # alternating 2-factor G
    G_edges = set()
    for l in range(n):
        ps = sorted([ (pts[tuple(sorted((l,m)))], m) for m in range(n) if m!=l ],
                    key=lambda t: (t[0][0], t[0][1]))
        # order along line: by x (if line not vertical) else by y
        if lines[l][1] == 0:  # vertical line a x = c -> order by y
            ps.sort(key=lambda t: t[0][1])
        for q in range(0, n-1, 2):
            G_edges.add(frozenset([tuple(sorted((l,ps[q][1]))), tuple(sorted((l,ps[q+1][1])))]))
    P_edges = set(frozenset([tuple(sorted(cyc[t])), tuple(sorted(cyc[(t+1)%k]))]) for t in range(k))
    # components of G
    adj = {}
    for e in G_edges:
        a,b = tuple(e); adj.setdefault(a,[]).append(b); adj.setdefault(b,[]).append(a)
    seen=set(); comps=0
    for v in adj:
        if v in seen: continue
        comps+=1; st=[v]
        while st:
            x=st.pop()
            if x in seen: continue
            seen.add(x); st.extend(adj[x])
    per_line = [side_line.count(l) for l in range(n)]
    print(f'n={n}: k={k}, simple=OK, general position=OK, lean data matches json=OK;',
          f'missing pairs={sorted(missing)} (triangle {d.get("triangle")}); sides per line={per_line};',
          f'G has {comps} components; polygon == G: {P_edges==G_edges}')
