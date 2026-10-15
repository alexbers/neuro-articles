structure Pt where
  x : Int
  y : Int
  w : Int
deriving Repr

structure Ln where
  a : Int
  b : Int
  c : Int
deriving Repr

def onLine (l : Ln) (p : Pt) : Bool := l.a * p.x + l.b * p.y == l.c * p.w

def orient (p q r : Pt) : Int :=
  p.x * (q.y * r.w - q.w * r.y) - p.y * (q.x * r.w - q.w * r.x) + p.w * (q.x * r.y - q.y * r.x)

def fle (u uw v vw : Int) : Bool := decide (u * vw ≤ v * uw)

def inBox (p q r : Pt) : Bool :=
  ((fle p.x p.w r.x r.w && fle r.x r.w q.x q.w) || (fle q.x q.w r.x r.w && fle r.x r.w p.x p.w)) &&
  ((fle p.y p.w r.y r.w && fle r.y r.w q.y q.w) || (fle q.y q.w r.y r.w && fle r.y r.w p.y p.w))

def segInter (a b c d : Pt) : Bool :=
  let d1 := orient c d a
  let d2 := orient c d b
  let d3 := orient a b c
  let d4 := orient a b d
  ((decide (d1 > 0) && decide (d2 < 0)) || (decide (d1 < 0) && decide (d2 > 0))) &&
    ((decide (d3 > 0) && decide (d4 < 0)) || (decide (d3 < 0) && decide (d4 > 0))) ||
  (d1 == 0 && inBox c d a) || (d2 == 0 && inBox c d b) ||
  (d3 == 0 && inBox a b c) || (d4 == 0 && inBox a b d)

def vtx (P : List Pt) (j : Nat) : Pt := P.getD (j % P.length) ⟨0, 0, 1⟩

def isSimplePolygon (P : List Pt) : Bool :=
  let k := P.length
  decide (3 ≤ k) &&
  P.all (fun p => decide (p.w > 0)) &&
  (List.range k).all (fun j => orient (vtx P j) (vtx P (j + 1)) (vtx P (j + 2)) != 0) &&
  (List.range k).all (fun i => (List.range k).all (fun j =>
    if decide (i + 2 ≤ j) && decide (j + 2 ≤ k + i) then
      !(segInter (vtx P i) (vtx P (i + 1)) (vtx P j) (vtx P (j + 1)))
    else true))

def sidesOnLines (L : List Ln) (P : List Pt) : Bool :=
  (List.range P.length).all (fun j =>
    L.any (fun l => onLine l (vtx P j) && onLine l (vtx P (j + 1))))

def genuineLines (L : List Ln) : Bool := L.all (fun l => l.a != 0 || l.b != 0)
