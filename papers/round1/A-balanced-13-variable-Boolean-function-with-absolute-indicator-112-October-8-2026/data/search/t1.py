import numpy as np, time
from orbits import *
n=13
rot = perm_action(n, [(i+1)%n for i in range(n)])
mul2 = perm_action(n, [(2*i)%n for i in range(n)])
t=time.time()
oid, reps = orbits(n, [rot, mul2])
k=len(reps); print('orbits', k, time.time()-t)
F = class_matrix(n, oid, k)
C = F[:, reps]  # C[i][j]
sizes = np.bincount(oid)
print(sizes[:10], C.shape)
np.save('agl13_C.npy', C); np.save('agl13_sizes.npy', sizes); np.save('agl13_oid.npy', oid)
