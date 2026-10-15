import sys
vals=dict(NROWSVAL=sys.argv[1], NW19VAL=sys.argv[2], NWOTHERVAL=sys.argv[3], NEFFVAL=sys.argv[4], NBOUNDVAL=sys.argv[5], NLEANVAL=sys.argv[6], NLNUMVAL=sys.argv[7], NLDENVAL=sys.argv[8])
s=open('build/main_template.tex').read()
for k,v in vals.items(): s=s.replace(k,v)
open('build/main.tex','w').write(s)
r=open('README.md').read().replace('NLNUM',sys.argv[7]).replace('NLDEN',sys.argv[8])
open('README.md','w').write(r)
