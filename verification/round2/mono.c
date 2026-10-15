/* count monochromatic K_k^(3) (k = 4 or 5) of colour chi in a 2-colouring of the triples of {0..n-1}
   usage: mono n k chi redfile   (redfile lists red triples) */
#include <stdio.h>
#include <stdlib.h>
static unsigned char C[128][128][128];
int main(int argc, char **argv) {
  int n = atoi(argv[1]), k = atoi(argv[2]), chi = atoi(argv[3]); FILE *f = fopen(argv[4], "r");
  int a, b, c; long cnt = 0;
  while (fscanf(f, "%d %d %d", &a, &b, &c) == 3) {
    int v[3] = {a, b, c};
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int l = 0; l < 3; l++)
      if (i != j && j != l && i != l) C[v[i]][v[j]][v[l]] = 1;
  }
  #define X(p,q,r) (C[p][q][r] == chi)
  for (a = 0; a < n; a++) for (b = a+1; b < n; b++) for (c = b+1; c < n; c++) if (X(a,b,c))
    for (int d = c+1; d < n; d++) if (X(a,b,d) && X(a,c,d) && X(b,c,d)) {
      if (k == 4) { cnt++; continue; }
      for (int e = d+1; e < n; e++)
        if (X(a,b,e) && X(a,c,e) && X(a,d,e) && X(b,c,e) && X(b,d,e) && X(c,d,e)) cnt++;
    }
  printf("n=%d k=%d colour=%s: %ld monochromatic K%d^(3)\n", n, k, chi ? "red" : "blue", cnt, k);
  return 0;
}
