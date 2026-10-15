theorem mo513798_n11 :
    ∃ (L : List Ln) (P : List Pt),
      L.length = 11 ∧ P.length = 55 ∧ genuineLines L = true ∧
      isSimplePolygon P = true ∧ sidesOnLines L P = true :=
  ⟨lines11, poly11, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
