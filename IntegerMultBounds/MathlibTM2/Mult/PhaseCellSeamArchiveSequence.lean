module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamArchiveNumericalState

/-! Structural execution of certified archive stages shares their workspace.
Stage execution remains a premise here; physical readiness is discharged by
the restoring seam executor when this combinator is instantiated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement
variable {T Q A s : ℕ} [NeZero s] {P U : Type}

theorem seamArchiveSequence_exec (body : P → Pr P T Q A U)
    (program : ℕ → Pr P T Q A U) (p width W : ℕ) (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hwidth : 0 < width) (classes : ℕ → CorePublicationClass s width)
    (src dst : Fin T) (hne : src ≠ dst) (sourceTail outputTail : List (Fin (A+4)))
    (S : Stacks T A) (depth : ℕ)
    (hstep : ∀ k ks (u : HS T Q A U) M,
      SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S (k::ks) M →
      ∃ u' F, ∃ n : ℕ, u'.user = u.user ∧ n ≤ 250*(r.inputs.length+1)*(s*W) ∧
        SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail M ks F ∧
        mnSize (mk u' F) ≤ mnSize (mk u M) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk u M)+depth+3250*(r.inputs.length+1)*(s*W))
          depth (program k) (mk u M) n (mk u' F))
    (ks : List ℕ) (hcount : ks.length ≤ 3) (v : HS T Q A U) (M : Stacks T A)
    (hInv : SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S ks M) :
    ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ n ≤ 750*(r.inputs.length+1)*(s*W)+1 ∧
      SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S [] F ∧
      F.R src = sourceTail ∧
      (∃ ambient : List (List (Fin (A+4))), F.R dst = ambient.flatten++outputTail ∧
        List.Forall₂ (fun target line => line.length = s*W ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
          (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
          (seamPublicationTargets p r J) ambient) ∧ mnSize (mk v' F) ≤ mnSize (mk v M) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v M)+depth+3250*(r.inputs.length+1)*(s*W))
        depth (restoringSequence program ks) (mk v M) n (mk v' F) := by
  obtain ⟨v',F,n,hu,hn,hF,hs,he⟩ := restoringSequence_exec_uniform body program
    (SeamArchiveNumericalState p width W r J classes src dst sourceTail outputTail S)
    (250*(r.inputs.length+1)*(s*W)) (3250*(r.inputs.length+1)*(s*W)) depth
    (by
      intro k rest u N hI
      obtain ⟨u',G,n,hu,hn,hG,hs,he⟩ := hstep k rest u N hI
      exact ⟨u',G,n,hu,hn,SeamArchiveNumericalState.rebase p width W r J classes src dst sourceTail outputTail
        S N G (k::rest) rest hI hG,hs,he⟩) ks v M hInv
  refine ⟨v',F,n,hu,?_,hF,?_,?_,hs,he⟩
  · have hh := Nat.mul_le_mul_right (250*(r.inputs.length+1)*(s*W)) hcount
    nlinarith
  · exact SeamArchiveState.nil_source p width W r J src dst hne sourceTail outputTail S F
      (hF.forget p width W r J classes src dst sourceTail outputTail S F [])
  · exact (hF.finish p width W hwidth r J classes src dst hne sourceTail outputTail S F).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
