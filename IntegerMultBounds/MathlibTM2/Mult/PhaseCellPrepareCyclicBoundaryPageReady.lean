module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicBoundaryPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPageReady

/-! The complete computed cyclic page producer returns reusable arithmetic readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem prepareCyclicBoundaryPage_ready_exec {s t band a n Psize Nstage q l u : ℕ} [NeZero s]
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : band ≤ s)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t) (hb : (S.R 124).length = band)
    (haSrc : (S.R 141).length = a) (hnSrc : (S.R 142).length = n)
    (hfresh : ∀ k ∈ [(106 : Fin 154),108,109,115,116,135,138,144,145,146], S.R k = [])
    (hlow : ∀ k : Fin 154, k.val < 77 → S.R k = []) (hleft : ∀ k, S.L k = []) (input : List (Fin (A+4)))
    (hready : LengthKeyReady Psize Nstage q l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg S)))) :
    let V := publicationGeometryWidth t band
    let N := (cyclicPrincipalBoundary s t band a n).card
    let output := cstream A V ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    let R := Function.update (Function.update (Function.update (Function.update (Function.update S.R
      141 []) 142 []) 144 (List.replicate a tick)) 145 (List.replicate (a+min n (s-a)) tick))
        146 (List.replicate (n-min n (s-a)) tick)
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCyclicBoundaryPageCost S.R s t band a n ∧
      Exec body prepareCyclicBoundaryPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update R
          115 (List.replicate V tick)) 116 (List.replicate N tick)) 109 output)}) ∧
      LengthKeyReady Psize Nstage q l s t u band 0 0 input
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg {S with R := (Function.update (Function.update (Function.update R
          115 (List.replicate V tick)) 116 (List.replicate N tick)) 109 output)}))) := by
  dsimp only
  obtain ⟨v',m,hu,hm,he⟩ := prepareCyclicBoundaryPage_exec (body := body)
    hst ha hn hband v S hs ht hb haSrc hnSrc hfresh hlow hleft
  refine ⟨v',m,hu,hm,he,?_⟩
  apply cyclicPageReady_of_frame hready
  · rfl
  · intro k hk
    have hne : k ≠ 109 ∧ k ≠ 115 ∧ k ≠ 116 ∧ k ≠ 141 ∧ k ≠ 142 ∧ k ≠ 144 ∧ k ≠ 145 ∧ k ≠ 146 := by
      simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hk
    rcases hne with ⟨h109,h115,h116,h141,h142,h144,h145,h146⟩
    simp [h109,h115,h116,h141,h142,h144,h145,h146]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
