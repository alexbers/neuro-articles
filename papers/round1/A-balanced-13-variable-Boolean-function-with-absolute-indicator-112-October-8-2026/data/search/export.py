import numpy as np, sys
def export(pre, C, sizes):
    k = C.shape[0]
    with open(pre + '.bin', 'wb') as fp:
        np.array([k], dtype=np.int32).tofile(fp)
        np.asarray(sizes, dtype=np.int32).tofile(fp)
        np.asarray(C, dtype=np.int32).tofile(fp)
if __name__ == '__main__':
    pre = sys.argv[1]
    export(pre, np.load(pre+'_C.npy'), np.load(pre+'_sizes.npy'))
