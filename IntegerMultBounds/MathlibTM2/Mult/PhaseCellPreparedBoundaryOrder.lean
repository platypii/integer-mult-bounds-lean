module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryOrderData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationWidth

/-! Prepare owned boundary coordinates, their word width and their counted cardinality. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedBoundaryOrder : Pr P₀ 117 Q A U :=
  .seq generatePublicationWidth (.seq boundaryOrderFromHeaders (countWords 115 109 116 106 108))

def preparedBoundaryOrderCost (s t band a b : ℕ) [NeZero s] : ℕ :=
  let V := publicationGeometryWidth t band
  generatePublicationWidthCost t band+boundaryOrderFromHeadersCost V s t band a b+
    (haloBoundary s t band a b).card*(6*V+6)+4

theorem preparedBoundaryOrder_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = [])
    (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    let V := publicationGeometryWidth t band
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedBoundaryOrderCost s t band a b ∧
      Exec body preparedBoundaryOrder (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          115 (List.replicate V tick)) 109 (boundaryOrderSymbols A V s t band a b))
          116 (List.replicate (haloBoundary s t band a b).card tick))}) := by
  dsimp only
  let V := publicationGeometryWidth t band
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generatePublicationWidth_exec (body := body)
    t band v S ht hband h115 (by
      intro k hk
      have hk31 : k.val < 31 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
      exact hblank k hk31)
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryOrderFromHeaders_exec (body := body)
    (V := V) (s := s) (t := t) (band := band) (a := a) (b := b) hst haS hbS hbandS
    (publicationGeometryWidth_fits t band) v₁ S₁
    (by simpa [S₁] using hs) (by simpa [S₁] using ht) (by simpa [S₁] using hband)
    (by simpa [S₁] using ha) (by simpa [S₁] using hb) (by simpa [S₁] using h108)
    (by simp [S₁]) (by simpa [S₁] using h106)
    (by intro k hk
        have hne : k ≠ 115 := by intro he; subst k; norm_num at hk
        simpa [S₁,hne] using hblank k hk)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 109 (boundaryOrderSymbols A (publicationGeometryWidth t band) s t band a b++S₁.R 109)}
  let words := (boundaryIndices s t band a b).map (fun k =>
    IntegerMultBounds.MathlibTM2.Fast.TableVM.tblPairs A V k 0)
  have hwords : words.flatten = boundaryOrderSymbols A V s t band a b := by
    simpa only [words,← List.flatMap_def] using (boundaryOrderSymbols_eq A V s t band a b).symm
  have hlen : words.length = (haloBoundary s t band a b).card := by
    simp only [words,List.length_map,boundaryIndices_length hst band a b hbS]
  obtain ⟨v₃,hu₃,he₃⟩ := countWords_exec (body := body)
    (width := 115) (src := 109) (dst := 116) (saved := 106) (tmp := 108) (by decide)
    V (by dsimp [V,publicationGeometryWidth]; omega) words
    (by intro xs hx; obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx; simp)
    v₂ S₂ (by simp [S₂,S₁]) (by simpa [S₂,S₁,h109,V] using hwords.symm)
    (by simpa [S₂,S₁] using h106) (by simpa [S₂,S₁] using h108)
  refine ⟨v₃,n₁+(n₂+((haloBoundary s t band a b).card*(6*V+6)+4)),
    hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_⟩
  · change n₁+(n₂+((haloBoundary s t band a b).card*(6*V+6)+4)) ≤
      generatePublicationWidthCost t band+boundaryOrderFromHeadersCost V s t band a b+
        (haloBoundary s t band a b).card*(6*V+6)+4
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [S₂,S₁,V,hlen,h109,h116,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
