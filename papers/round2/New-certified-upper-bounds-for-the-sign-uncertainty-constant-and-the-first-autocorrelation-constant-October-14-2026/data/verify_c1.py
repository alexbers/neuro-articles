# Independent exact check of the C1 certificate (no Kronecker): split heights into 20-bit halves,
# exact int64 convolutions (numpy direct), recombine with Python ints.
import numpy as np, sys, json
from fractions import Fraction
A=np.load(sys.argv[1]).astype(np.int64)        # integer heights 0..2^40
meta=json.load(open(sys.argv[2]))
n=len(A); assert A.min()>=0 and A.max()<=2**40
hi=A>>20; lo=A&((1<<20)-1)
chh=np.convolve(hi,hi); chl=np.convolve(hi,lo); cll=np.convolve(lo,lo)   # each < 2^16*2^40 = 2^56
c=[(int(a)<<40)+(int(b)<<21)+int(d) for a,b,d in zip(chh,chl,cll)]
M=max(c); S=int(A.sum())
assert M==int(meta['M']) and S==int(meta['S'])
B=Fraction(2*n*M,S*S); p=int(meta['p']); q=int(meta['q'])
print('n',n,'max conv',M,'sum',S,'exact 2nM/S^2 =',float(B),' <= p/q =',p/q, B<=Fraction(p,q))
