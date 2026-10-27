module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedTransferLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

/-! Apply a generated halo mask in one scan, preserving the original ambient source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

def maskCouplingSource : Pr P 144 Q A U :=
  .seq (copyCountedLine 97 94 110 142 108 104 105)
    (.seq (ucopy 97 143 135)
      (.seq (maskedTransferLine 143 94 109 142 107 104 105) (moveR 107 141 id)))

def maskCouplingSourceCost (s w : ℕ) : ℕ := s*(28*w+28)+24

theorem maskCouplingSource_exec (hA : 4 ≤ A) (flags : List Bool) (xs : List GaussianInt)
    (w : ℕ) (hlen : xs.length = flags.length) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = flags.length) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = cstream A w xs++tail)
    (hmask : S.R 109 = flags.map (fun flag => pairSym A flag flag))
    (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h107 : S.R 107 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ maskCouplingSourceCost flags.length w ∧
      Exec body maskCouplingSource (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 109 [])
          141 (cstream A w (maskedLine flags xs)++S.R 141))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := copyCountedLine_exec (body := body)
    97 94 110 142 108 104 105 (by decide) flags.length w (cstream A w xs) tail
    (by simp [hlen]) v S hs hw hsrc h108 h104 h105
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 142 (cstream A w xs++S.R 142)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (show (97 : Fin 144) ≠ 143 by decide)
    (show (97 : Fin 144) ≠ 135 by decide) (show (143 : Fin 144) ≠ 135 by decide)
    v₁ S₁ (by simpa [S₁] using h135)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 143 (List.replicate flags.length tick)}
  have he₂' : Exec body (ucopy 97 143 135) (mk v₁ S₁) (4*flags.length+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hs,h143] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := maskedTransferLine_exec (body := body)
    (count := 143) (width := 94) (mask := 109) (src := 142) (dst := 107)
    (trash := 104) (tmp := 105) (by decide) hA flags xs w hlen (S.R 142) v₂ S₂
    (by simp [S₂]) (by simpa [S₂,S₁] using hw) (by simpa [S₂,S₁] using hmask)
    (by simp [S₂,S₁]) (by simpa [S₂,S₁] using h104) (by simpa [S₂,S₁] using h105)
  let words := cstream A w (maskedLine flags xs)
  let S₃ : Stacks 144 A := {S₂ with R := (Function.update (Function.update (Function.update
    (Function.update S₂.R 109 []) 142 (S.R 142)) 107 words.reverse) 143 [])}
  have he₃' : Exec body (maskedTransferLine 143 94 109 142 107 104 105) (mk v₂ S₂) m₃ (mk v₃ S₃) := by
    simpa [S₃,words,S₂,S₁,h107] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 107 141 (by decide) id v₃ S₃
  have hwords : words.length = flags.length*w := by simp [words,hlen]
  refine ⟨v₄,m₁+((4*flags.length+4)+(m₃+(2*(flags.length*w)+2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · dsimp only [maskCouplingSourceCost,copyCountedLineCost] at *
    nlinarith only [hm₁,hm₃]
  · simp [S₃,hwords]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h109 : k = 109 <;> by_cases h142 : k = 142 <;>
      by_cases h107' : k = 107 <;> by_cases h143' : k = 143 <;> by_cases h141 : k = 141 <;>
      simp [S₃,S₂,S₁,movedR,h109,h142,h107',h143',h141,h107,h143,words,Function.update_apply]

theorem maskedLine_halo {s : ℕ} [NeZero s] (boundary : Bool) (t band a b : ℕ)
    (hst : s < t) (hb : b ≤ s) (C : ZMod s → GaussianInt) :
    maskedLine ((List.range s).map (fun k => haloMaskAt boundary s t band a b k)) (chirpLine s C) =
      chirpLine s (fun j => if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
        then C j else 0) := by
  apply List.ext_getElem
  · simp [maskedLine,chirpLine]
  · intro k hk hk'
    have hks : k < s := by simpa [maskedLine,chirpLine] using hk
    have hmem := haloMaskAt_spec boundary hst band a b k hb hks
    simp only [maskedLine,List.getElem_zipWith,chirpLine,List.getElem_map,List.getElem_range]
    simp only [hmem]

theorem maskCouplingSource_halo_exec {s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (boundary : Bool) (t band a b w : ℕ) (hst : s < t) (hb : b ≤ s)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hw : (S.R 94).length = w)
    (hsrc : S.R 110 = cstream A w (chirpLine s C)++tail)
    (hmask : S.R 109 = couplingSourceMaskSymbols boundary A s t band a b)
    (h108 : S.R 108 = []) (h104 : S.R 104 = []) (h105 : S.R 105 = [])
    (h135 : S.R 135 = []) (h107 : S.R 107 = []) (h143 : S.R 143 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ maskCouplingSourceCost s w ∧
      Exec body maskCouplingSource (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 109 [])
          141 (cstream A w (chirpLine s (fun j =>
            if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
            then C j else 0))++S.R 141))}) := by
  let flags := (List.range s).map (fun k => haloMaskAt boundary s t band a b k)
  obtain ⟨v',m,hu,hm,he⟩ := maskCouplingSource_exec (body := body) hA flags (chirpLine s C) w
    (by simp [flags]) tail v S (by simpa [flags] using hs) hw hsrc
    (by simpa [flags,couplingSourceMaskSymbols,List.map_map,Function.comp_def] using hmask)
    h108 h104 h105 h135 h107 h143
  refine ⟨v',m,hu,by simpa [flags] using hm,?_⟩
  simpa only [flags,maskedLine_halo boundary t band a b hst hb C] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
