module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine

/-! Retain the original RHS before the periodic residual consumes its working
copy. Only the native input queue changes; the factory invariant is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

theorem PackedHaloBetweenInputs.update_source
    {A precision stage q l s t u band a b V w W N : ℕ} {S : Stacks 248 A}
    (h : PackedHaloBetweenInputs precision stage q l s t u band a b V w W N S)
    (words : List (Fin (A+4))) :
    PackedHaloBetweenInputs precision stage q l s t u band a b V w W N
      {S with R := Function.update S.R 110 words} := by
  constructor
  · apply h.bank.of_runtime_frame (F := embStk packedBoundaryRecoveryBase
      {S with R := Function.update S.R 110 words}) rfl
    · intro k hk
      have hn : packedBoundaryRecoveryBase k ≠ 110 := by
        intro he; have hv := congrArg (fun i : Fin 248 => i.val) he
        change k.val = 110 at hv
        omega
      simp [embStk,hn]
    · simp [embStk,packedBoundaryRecoveryBase]
    · intro k hk _
      have hn : packedBoundaryRecoveryBase k ≠ 110 := by
        intro he; have hv := congrArg (fun i : Fin 248 => i.val) he
        change k.val = 110 at hv
        omega
      simp [embStk,hn]
  · apply h.headers.of_frame
    intro k hk
    have hr := haloRetainedHeaderPorts_safe k hk
    have hn : packedRecoveryRuntimeReg k ≠ 110 := by
      intro he; have hv := congrArg (fun i : Fin 248 => i.val) he
      change k.val = 110 at hv
      omega
    simp [embStk,hn]
  · intro i h93 h110
    have hn : (⟨i.val,by omega⟩ : Fin 248) ≠ 110 := by
      intro he; exact h110 (Fin.ext (congrArg (fun k : Fin 248 => k.val) he))
    simpa only [Function.update_of_ne hn] using h.native i h93 h110
  · intro k hk
    have hc : ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 248)).all
        (fun k => decide (k ≠ 110)) = true := by decide +kernel
    have hn := of_decide_eq_true (List.all_eq_true.mp hc k hk)
    simpa only [Function.update_of_ne hn] using h.scratch k hk
  · simpa using h.binaryLength
  · intro k hk
    have hn : k ≠ 110 := by
      intro he; have hv := congrArg (fun i : Fin 248 => i.val) he
      omega
    simpa only [Function.update_of_ne hn] using h.privateBank k hk

def periodicRetainRhs {Q A : ℕ} {P U : Type} : Pr P 242 Q A U :=
  copyCountedLine 121 174 93 110 125 127 128

theorem periodicRetainRhs_exec {Q A precision stage q l s t u band a b V w W N : ℕ}
    {P U : Type} {body : P → Pr P 242 Q A U}
    (words tail : List (Fin (A+4))) (hlen : words.length = s*w)
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : PackedHaloBetweenInputs precision stage q l s t u band a b V w W N
      (extendStacks (by decide) S)) (hsource : S.R 93 = words++tail) :
    let F := {S with R := Function.update S.R 110 (words++S.R 110)}
    ∃ v' n, v'.user = v.user ∧ n ≤ copyCountedLineCost s w ∧
      Exec body periodicRetainRhs (mk v S) n (mk v' F) ∧
      PackedHaloBetweenInputs precision stage q l s t u band a b V w W N
        (extendStacks (by decide) F) ∧
      ∀ bo hf df, PackedBoundaryFactorPages bo hf df S → PackedBoundaryFactorPages bo hf df F := by
  dsimp only
  have hbank := h.bank
  simp only [packedBoundaryRecoveryBase,embStk_extendStacks] at hbank
  have hs : (S.R 121).length = s := by
    simpa [embStk,packedRecoveryRuntimeReg,extendStacks] using h.headers.masters.axis
  obtain ⟨v',n,hu,hn,he⟩ := copyCountedLine_exec (body := body)
    121 174 93 110 125 127 128 (by decide) s w words tail hlen v S hs
    (packedBoundaryRecovery_width hbank.ready) hsource
    (h.scratch 125 (by decide)) (h.scratch 127 (by decide)) (h.scratch 128 (by decide))
  refine ⟨v',n,hu,hn,he,?_,?_⟩
  · rw [extendStacks_updateR]
    exact h.update_source (words++S.R 110)
  · intro bo hf df hpages
    apply hpages.of_solution_frame
    intro k hk _
    have hn : k ≠ 110 := by
      intro he; have hv := congrArg (fun i : Fin 242 => i.val) he
      omega
    simp [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
