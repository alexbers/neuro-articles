/-!
# MathOverflow 513798: simple polygons whose sides lie on few lines

Question (MO 513798, 2026-07-31, "What is the maximum k for a k-gon inducible with an n-line
arrangement?"): if a simple polygon has `k` sides and the sides lie on `n` lines, then
`k ≤ n * ⌊(n-1)/2⌋`; the asker conjectured this bound is attained for every `n`, but had examples only
for `n ≤ 6` (DSM found one for `n = 8` in the comments) and reported failure for `n = 7` and `n = 11`.

This file certifies the *constructions* of the answer (see the paper, `paper.pdf`, for the full answer):

* `mo513798_n11` : 11 lines carrying a simple 55-gon  (55 = 11 * 5, the bound is attained);
* `mo513798_n13` : 13 lines carrying a simple 78-gon  (78 = 13 * 6, the bound is attained);
* `mo513798_n7`  : 7 lines carrying a simple 18-gon   (the paper proves 18 is optimal for n = 7);
* `mo513798_n9`  : 9 lines carrying a simple 33-gon   (the paper proves 33 is optimal for n = 9).

The matching upper bounds for `n = 7, 9` (no simple 21-gon on 7 lines, no simple 36-gon on 9 lines;
more generally no simple `n(n-1)/2`-gon on `n` lines when `n ≡ ±1 (mod 8)`) are proved on paper in
Sections 2-3 of `paper.pdf` and are NOT part of this Lean file.

Everything below is checked by kernel evaluation (`decide +kernel`) with exact integer arithmetic;
no Mathlib, no `native_decide`, no `sorry`.

Conventions.  A point of `ℚ²` is stored in homogeneous integer coordinates `(x, y, w)` meaning
`(x / w, y / w)`; only `w > 0` is allowed (and this is checked).  A line `⟨a, b, c⟩` is the set
`{(X, Y) | a X + b Y = c}`.
-/

/-- The point `(x / w, y / w)` of the rational plane (valid when `w > 0`). -/
structure Pt where
  x : Int
  y : Int
  w : Int
deriving Repr

/-- The line `{(X, Y) | a * X + b * Y = c}`; it is a genuine line iff `(a, b) ≠ (0, 0)`. -/
structure Ln where
  a : Int
  b : Int
  c : Int
deriving Repr

/-- `p` lies on `l`:  `a * (x/w) + b * (y/w) = c`, multiplied through by `w`. -/
def onLine (l : Ln) (p : Pt) : Bool := l.a * p.x + l.b * p.y == l.c * p.w

/-- `det [[p.x, p.y, p.w], [q.x, q.y, q.w], [r.x, r.y, r.w]]`.  When `p.w, q.w, r.w > 0` this equals
`p.w * q.w * r.w` times the usual orientation `(q - p) × (r - p)` of the affine points, so its sign
is the orientation of the triangle `p q r` (`0` iff the three points are collinear). -/
def orient (p q r : Pt) : Int :=
  p.x * (q.y * r.w - q.w * r.y) - p.y * (q.x * r.w - q.w * r.x) + p.w * (q.x * r.y - q.y * r.x)

/-- `u / uw ≤ v / vw` (for `uw, vw > 0`). -/
def fle (u uw v vw : Int) : Bool := decide (u * vw ≤ v * uw)

/-- `r` lies in the closed axis-parallel bounding box of `p` and `q`. -/
def inBox (p q r : Pt) : Bool :=
  ((fle p.x p.w r.x r.w && fle r.x r.w q.x q.w) || (fle q.x q.w r.x r.w && fle r.x r.w p.x p.w)) &&
  ((fle p.y p.w r.y r.w && fle r.y r.w q.y q.w) || (fle q.y q.w r.y r.w && fle r.y r.w p.y p.w))

/-- The closed segments `[a, b]` and `[c, d]` have a common point.  This is the standard exact
test (Cormen–Leiserson–Rivest–Stein, *Introduction to Algorithms*, §33.1 `SEGMENTS-INTERSECT`):
proper crossing, or an endpoint of one segment lying on the other segment. -/
def segInter (a b c d : Pt) : Bool :=
  let d1 := orient c d a
  let d2 := orient c d b
  let d3 := orient a b c
  let d4 := orient a b d
  ((decide (d1 > 0) && decide (d2 < 0)) || (decide (d1 < 0) && decide (d2 > 0))) &&
    ((decide (d3 > 0) && decide (d4 < 0)) || (decide (d3 < 0) && decide (d4 > 0))) ||
  (d1 == 0 && inBox c d a) || (d2 == 0 && inBox c d b) ||
  (d3 == 0 && inBox a b c) || (d4 == 0 && inBox a b d)

/-- The `j`-th vertex of the closed polygon `P` (indices taken mod `P.length`). -/
def vtx (P : List Pt) (j : Nat) : Pt := P.getD (j % P.length) ⟨0, 0, 1⟩

/-- `P` (vertices listed in cyclic order) is a simple polygon with `P.length` sides:
* at least 3 vertices, all valid points (`w > 0`);
* every corner is a genuine corner: `P j`, `P (j+1)`, `P (j+2)` are never collinear
  (so consecutive vertices are distinct and consecutive sides are not collinear);
* any two non-adjacent sides `[P i, P (i+1)]`, `[P j, P (j+1)]` (`i + 2 ≤ j`, `j + 2 ≤ k + i`)
  are disjoint closed segments.
Together these say exactly that the closed polygonal chain is a simple closed curve whose
`k` sides are genuine sides (adjacent sides meet only in their common vertex, since they are
not collinear). -/
def isSimplePolygon (P : List Pt) : Bool :=
  let k := P.length
  decide (3 ≤ k) &&
  P.all (fun p => decide (p.w > 0)) &&
  (List.range k).all (fun j => orient (vtx P j) (vtx P (j + 1)) (vtx P (j + 2)) != 0) &&
  (List.range k).all (fun i => (List.range k).all (fun j =>
    if decide (i + 2 ≤ j) && decide (j + 2 ≤ k + i) then
      !(segInter (vtx P i) (vtx P (i + 1)) (vtx P j) (vtx P (j + 1)))
    else true))

/-- Every side `[P j, P (j+1)]` of the polygon lies on one of the lines of `L`. -/
def sidesOnLines (L : List Ln) (P : List Pt) : Bool :=
  (List.range P.length).all (fun j =>
    L.any (fun l => onLine l (vtx P j) && onLine l (vtx P (j + 1))))

/-- All lines of `L` are genuine lines. -/
def genuineLines (L : List Ln) : Bool := L.all (fun l => l.a != 0 || l.b != 0)


/-! ### Sanity checks of the checker (it accepts a square, rejects degenerate / self-intersecting ones) -/

/-- unit square -/
example : isSimplePolygon [⟨0, 0, 1⟩, ⟨1, 0, 1⟩, ⟨1, 1, 1⟩, ⟨0, 1, 1⟩] = true := by decide +kernel
/-- bow-tie (self-intersecting) -/
example : isSimplePolygon [⟨0, 0, 1⟩, ⟨1, 1, 1⟩, ⟨1, 0, 1⟩, ⟨0, 1, 1⟩] = false := by decide +kernel
/-- a "corner" with three collinear consecutive vertices is rejected -/
example : isSimplePolygon [⟨0, 0, 1⟩, ⟨1, 0, 2⟩, ⟨1, 0, 1⟩, ⟨0, 1, 1⟩] = false := by decide +kernel
/-- a polygon that touches itself (vertex on a non-adjacent side) is rejected -/
example : isSimplePolygon [⟨0, 0, 1⟩, ⟨4, 0, 1⟩, ⟨4, 4, 1⟩, ⟨2, 0, 1⟩, ⟨0, 4, 1⟩] = false := by decide +kernel
/-- collinear overlapping segments intersect; collinear disjoint ones do not -/
example : segInter ⟨0, 0, 1⟩ ⟨2, 0, 1⟩ ⟨1, 0, 1⟩ ⟨3, 0, 1⟩ = true := by decide +kernel
example : segInter ⟨0, 0, 1⟩ ⟨1, 0, 1⟩ ⟨2, 0, 1⟩ ⟨3, 0, 1⟩ = false := by decide +kernel
/-- homogeneous coordinates: (1/2, 0) lies on [(0,0),(1,0)] -/
example : segInter ⟨0, 0, 1⟩ ⟨1, 0, 1⟩ ⟨1, 0, 2⟩ ⟨1, 5, 1⟩ = true := by decide +kernel
example : onLine ⟨1, 1, 1⟩ ⟨1, 1, 2⟩ = true := by decide +kernel


/-! ### n = 7 : a simple 18-gon on 7 lines -/

/-- The 7 lines `a*x + b*y = c` of the arrangement. -/
def lines7 : List Ln := [
  ⟨-6, 17, -74⟩,
  ⟨0, -19, -95⟩,
  ⟨-19, 14, -98⟩,
  ⟨4, -7, 8⟩,
  ⟨-19, 13, -44⟩,
  ⟨8, 11, 41⟩,
  ⟨-6, 2, -41⟩]

/-- The 18 vertices of the polygon, in cyclic order, as points `(x/w, y/w)`. -/
def poly7 : List Pt := [
  ⟨53, 10, 2⟩,
  ⟨1511, -346, 202⟩,
  ⟨13, -2, 2⟩,
  ⟨61, -22, 10⟩,
  ⟨630, -818, 239⟩,
  ⟨-658, -1026, 19⟩,
  ⟨-214, -1142, 245⟩,
  ⟨-191, -124, 13⟩,
  ⟨68, 8, 27⟩,
  ⟨1017, 427, 313⟩,
  ⟨-7, 20, 4⟩,
  ⟨109, 95, 19⟩,
  ⟨89, 103, 8⟩,
  ⟨17, 10, 2⟩,
  ⟨168, 95, 19⟩,
  ⟨378, 191, 46⟩,
  ⟨271, 116, 34⟩,
  ⟨43, 20, 4⟩]

/-! ### n = 9 : a simple 33-gon on 9 lines -/

/-- The 9 lines `a*x + b*y = c` of the arrangement. -/
def lines9 : List Ln := [
  ⟨-22, 6, -118⟩,
  ⟨-14, -23, 103⟩,
  ⟨18, -2, 91⟩,
  ⟨11, -6, -43⟩,
  ⟨-24, 1, -136⟩,
  ⟨27, 23, 49⟩,
  ⟨-3, 8, -149⟩,
  ⟨14, -2, -14⟩,
  ⟨16, 21, -33⟩]

/-- The 33 vertices of the polygon, in cyclic order, as points `(x/w, y/w)`. -/
def poly9 : List Pt := [
  ⟨155, -61, 32⟩,
  ⟨752, -527, 167⟩,
  ⟨2191, -1575, 468⟩,
  ⟨9, -10, 2⟩,
  ⟨2823, -2968, 520⟩,
  ⟨1059, -832, 193⟩,
  ⟨1788, -1675, 199⟩,
  ⟨15, -13, 1⟩,
  ⟨2603, -2395, 181⟩,
  ⟨3496, -3467, 299⟩,
  ⟨67, -68, 5⟩,
  ⟨313, -1056, 63⟩,
  ⟨3025, -4376, 566⟩,
  ⟨111, -184, 26⟩,
  ⟨430, -2409, 138⟩,
  ⟨25, -1462, 79⟩,
  ⟨-8, -49, 1⟩,
  ⟨-205, -1064, 53⟩,
  ⟨-619, -884, 35⟩,
  ⟨-1607, -531, 337⟩,
  ⟨-264, -623, 175⟩,
  ⟨-180, -119, 163⟩,
  ⟨-1101, 325, 327⟩,
  ⟨-139, 340, 83⟩,
  ⟨-28, 133, 47⟩,
  ⟨1, 224, 31⟩,
  ⟨859, 2528, 133⟩,
  ⟨143, 1120, 17⟩,
  ⟨105, 763, 4⟩,
  ⟨632, 1775, 86⟩,
  ⟨161, 374, 11⟩,
  ⟨349, 80, 61⟩,
  ⟨181, 264, 30⟩]

/-! ### n = 11 : a simple 55-gon on 11 lines -/

/-- The 11 lines `a*x + b*y = c` of the arrangement. -/
def lines11 : List Ln := [
  ⟨-39, 31, -51⟩,
  ⟨1, 50, 7⟩,
  ⟨-22, 45, -264⟩,
  ⟨12, -49, -212⟩,
  ⟨-10, -49, -25⟩,
  ⟨-16, 48, 31⟩,
  ⟨48, -14, 68⟩,
  ⟨-19, 46, -80⟩,
  ⟨-50, 3, 89⟩,
  ⟨17, 47, 93⟩,
  ⟨15, 48, 37⟩]

/-- The 55 vertices of the polygon, in cyclic order, as points `(x/w, y/w)`. -/
def poly11 : List Pt := [
  ⟨2767, 222, 1981⟩,
  ⟨-134, -2151, 1205⟩,
  ⟨-4334, -5691, 2243⟩,
  ⟨-2912, -6021, 1433⟩,
  ⟨-5889, -9174, 1073⟩,
  ⟨-369, -1166, 168⟩,
  ⟨-725, -3836, 278⟩,
  ⟨-159, -2794, 463⟩,
  ⟨14337, -3146, 1731⟩,
  ⟨2725, -766, 111⟩,
  ⟨3382, -505, 363⟩,
  ⟨14061, -2090, 1528⟩,
  ⟨16593, -2442, 1799⟩,
  ⟨4321, 26, 803⟩,
  ⟨2703, -22, 229⟩,
  ⟨11238, 3916, 269⟩,
  ⟨8657, 3020, 208⟩,
  ⟨14067, 4906, 336⟩,
  ⟨8544, 3256, 157⟩,
  ⟨13672, 4988, 379⟩,
  ⟨9071, 8880, 1539⟩,
  ⟨3409, 2025, 1376⟩,
  ⟨5266, 1869, 176⟩,
  ⟨8038, 407, 1675⟩,
  ⟨132, 69, 59⟩,
  ⟨3595, 678, 2337⟩,
  ⟨757, 34, 351⟩,
  ⟨4322, 53, 996⟩,
  ⟨390, -25, 107⟩,
  ⟨613, 5, 255⟩,
  ⟨5542, -497, 1602⟩,
  ⟨1004, -1274, 971⟩,
  ⟨1749, 134, 1207⟩,
  ⟨907, 45, 451⟩,
  ⟨1841, 260, 1246⟩,
  ⟨697, 102, 471⟩,
  ⟨3274, 465, 2221⟩,
  ⟨-319, 710, 1264⟩,
  ⟨288, 1057, 1488⟩,
  ⟨1891, 378, 1257⟩,
  ⟨1849, 1288, 1040⟩,
  ⟨3007, 2015, 1568⟩,
  ⟨2249, 1654, 1247⟩,
  ⟨525, 916, 182⟩,
  ⟨-3725, 9532, 2414⟩,
  ⟨-3904, 6163, 2401⟩,
  ⟨-5407, 4720, 1397⟩,
  ⟨-8363, 3624, 1311⟩,
  ⟨-4161, 3185, 2445⟩,
  ⟨-2143, 1070, 1240⟩,
  ⟨-833, 220, 98⟩,
  ⟨-10257, 296, 649⟩,
  ⟨-4429, 439, 2503⟩,
  ⟨-199, 6, 112⟩,
  ⟨-1214, 143, 848⟩]

/-! ### n = 13 : a simple 78-gon on 13 lines -/

/-- The 13 lines `a*x + b*y = c` of the arrangement. -/
def lines13 : List Ln := [
  ⟨5, -19, 255⟩,
  ⟨17, 11, 229⟩,
  ⟨-4, 20, -1118⟩,
  ⟨14, -14, 106⟩,
  ⟨19, 4, 126⟩,
  ⟨3, -20, -505⟩,
  ⟨-6, 19, -402⟩,
  ⟨10, 17, 78⟩,
  ⟨20, -3, -68⟩,
  ⟨-1, 20, 240⟩,
  ⟨18, -8, 29⟩,
  ⟨7, -19, -397⟩,
  ⟨-20, -3, -59⟩]

/-- The 78 vertices of the polygon, in cyclic order, as points `(x/w, y/w)`. -/
def poly13 : List Pt := [
  ⟨3578, -1595, 189⟩,
  ⟨1138, -1405, 127⟩,
  ⟨1094, -125, 161⟩,
  ⟨1447, 16, 189⟩,
  ⟨1830, 222, 283⟩,
  ⟨1124, 1717, 224⟩,
  ⟨1117, 1114, 386⟩,
  ⟨769, 970, 310⟩,
  ⟨559, 482, 214⟩,
  ⟨-221, -751, 70⟩,
  ⟨572, -647, 161⟩,
  ⟨1886, -4805, 395⟩,
  ⟨-1489, -4445, 302⟩,
  ⟨-631, -1804, 106⟩,
  ⟨-2057, -5440, 365⟩,
  ⟨-389, -760, 49⟩,
  ⟨-635, -1536, 119⟩,
  ⟨-461, 1120, 185⟩,
  ⟨-360, 354, 31⟩,
  ⟨-640, 4732, 397⟩,
  ⟨-101, 7464, 359⟩,
  ⟨-5267, 4516, 309⟩,
  ⟨-7025, 5284, 251⟩,
  ⟨-1060, 43, 8⟩,
  ⟨-3380, 1283, 121⟩,
  ⟨-6194, -1885, 19⟩,
  ⟨-8071, -2285, 12⟩,
  ⟨-14591, -4707, 32⟩,
  ⟨-15181, -5196, 19⟩,
  ⟨-6601, -2550, 22⟩,
  ⟨-3383, -3807, 56⟩,
  ⟨-139, -192, 7⟩,
  ⟨-2665, -7062, 294⟩,
  ⟨-51, -122, 2⟩,
  ⟨-2357, -11316, 194⟩,
  ⟨-1249, -4224, 181⟩,
  ⟨2327, -7686, 398⟩,
  ⟨2267, -11062, 206⟩,
  ⟨3496, -10369, 198⟩,
  ⟨4002, -6882, 385⟩,
  ⟨8773, -5460, 389⟩,
  ⟨2813, -3015, 64⟩,
  ⟨10283, -5434, 134⟩,
  ⟨2079, -888, 73⟩,
  ⟨12600, 1842, 101⟩,
  ⟨13580, 1039, 30⟩,
  ⟨16230, 2687, 10⟩,
  ⟨14695, 3290, 43⟩,
  ⟨2793, 480, 19⟩,
  ⟨17635, 4236, 63⟩,
  ⟨4595, 3694, 119⟩,
  ⟨631, 525, 14⟩,
  ⟨1655, 2344, 83⟩,
  ⟨220, 437, 16⟩,
  ⟨3727, 7349, 286⟩,
  ⟨806, 8425, 389⟩,
  ⟨500, 9973, 392⟩,
  ⟨155, 9896, 391⟩,
  ⟨106, 3812, 137⟩,
  ⟨-142, 1399, 23⟩,
  ⟨-335, 10277, 409⟩,
  ⟨-975, 9272, 373⟩,
  ⟨-61, 5736, 271⟩,
  ⟨-27, 2540, 120⟩,
  ⟨-38, 3577, 169⟩,
  ⟨-1, 522, 25⟩,
  ⟨-70, 8353, 401⟩,
  ⟨460, 4859, 403⟩,
  ⟨260, 781, 64⟩,
  ⟨10, 47, 3⟩,
  ⟨1940, 4309, 351⟩,
  ⟨2500, 4349, 352⟩,
  ⟨2151, 3629, 334⟩,
  ⟨1093, 351, 98⟩,
  ⟨2740, 1733, 133⟩,
  ⟨3220, 485, 27⟩,
  ⟨5817, -2160, 275⟩,
  ⟨3035, -964, 179⟩]

/-! ### Main theorems -/

/-- **Main theorem, n = 11.**  There are 11 lines and a simple polygon with `55 = 11 * ⌊(11-1)/2⌋` sides, each side lying on one of the lines: the upper bound `k ≤ n * ⌊(n-1)/2⌋` is attained for `n = 11`. -/
theorem mo513798_n11 :
    ∃ (L : List Ln) (P : List Pt),
      L.length = 11 ∧ P.length = 55 ∧ genuineLines L = true ∧
      isSimplePolygon P = true ∧ sidesOnLines L P = true :=
  ⟨lines11, poly11, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- **n = 13.**  There are 13 lines and a simple polygon with `78 = 13 * ⌊(13-1)/2⌋` sides, each side lying on one of the lines: the bound is attained for `n = 13`. -/
theorem mo513798_n13 :
    ∃ (L : List Ln) (P : List Pt),
      L.length = 13 ∧ P.length = 78 ∧ genuineLines L = true ∧
      isSimplePolygon P = true ∧ sidesOnLines L P = true :=
  ⟨lines13, poly13, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- **n = 7, lower bound.**  There are 7 lines and a simple polygon with 18 sides, each side lying on one of the lines.  (Paper: 19, 20, 21 are impossible, so the maximum for n = 7 is 18, not 21.) -/
theorem mo513798_n7 :
    ∃ (L : List Ln) (P : List Pt),
      L.length = 7 ∧ P.length = 18 ∧ genuineLines L = true ∧
      isSimplePolygon P = true ∧ sidesOnLines L P = true :=
  ⟨lines7, poly7, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- **n = 9, lower bound.**  There are 9 lines and a simple polygon with 33 sides, each side lying on one of the lines.  (Paper: 34, 35, 36 are impossible, so the maximum for n = 9 is 33, not 36.) -/
theorem mo513798_n9 :
    ∃ (L : List Ln) (P : List Pt),
      L.length = 9 ∧ P.length = 33 ∧ genuineLines L = true ∧
      isSimplePolygon P = true ∧ sidesOnLines L P = true :=
  ⟨lines9, poly9, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

#print axioms mo513798_n11
#print axioms mo513798_n13
#print axioms mo513798_n7
#print axioms mo513798_n9
