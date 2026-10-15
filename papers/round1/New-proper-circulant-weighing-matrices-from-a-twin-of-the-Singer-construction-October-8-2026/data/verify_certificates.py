# Independent plain-Python check of cert/certificates.json (O(n*k) exact integer arithmetic)
import json, math, sys
C=json.load(open(sys.argv[1] if len(sys.argv)>1 else 'certificates.json'))
ok_all=True
for name,v in C.items():
    a=v['seq']; n=v['n']; k=v['k']
    assert len(a)==n and all(x in (-1,0,1) for x in a)
    supp=[i for i in range(n) if a[i]]
    paf=[0]*n
    for i in supp:
        for j in supp:
            paf[(j-i)%n]+=a[i]*a[j]
    cw = paf[0]==k and all(x==0 for x in paf[1:])
    proper = all(len({i%e for i in supp})>1 for e in range(2,n+1) if n%e==0)
    s=int(round(math.isqrt(k)))
    print(f'{name}: n={n} k={k}=({s})^2 weight={len(supp)} P={sum(1 for x in a if x==1)} N={sum(1 for x in a if x==-1)} CW={cw} proper={proper}')
    ok_all&=cw and proper
print('ALL OK' if ok_all else 'FAIL')
