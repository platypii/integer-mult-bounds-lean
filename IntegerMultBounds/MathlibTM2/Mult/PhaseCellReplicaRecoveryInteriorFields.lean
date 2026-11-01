module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaHaloOutput

/-! Apply recovery acceptance to the actual encoded output rows of the shared
second pass. The eventual selector needs no further numerical argument. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T A : ℕ} [NeZero s]

theorem ReplicaRecoveryBatch.accept_output {H : ReplicaHaloProblem s} {target : ℕ}
    {X : ℕ → ZMod s → ℝ} (B : ReplicaRecoveryBatch H target X) (htarget)
    (dst : Fin T) (tail : List (Fin (A+4))) (F : Stacks T A)
    (h : RealReplicaHaloOutput (B.problem htarget) dst tail F) :
    ∃ Ds : List (ZMod s → GaussianInt), Ds.length = H.Fs.length ∧
      F.R dst = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))++tail ∧
      ∀ r : Fin H.Fs.length,
        (∀ i, Fits H.wordWidth (B.recoveredField r (Ds.getD r.val (fun _ => 0)) i)) ∧
        PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
          (fun i => (value H.precision (B.recoveredField r (Ds.getD r.val (fun _ => 0)) i)).re)
          (X r.val) (1/(2 : ℝ)^target) := by
  obtain ⟨Ds,hlen,hencoded,hrows⟩ := h
  obtain ⟨_,_,hw,_⟩ := B.problem_sizing htarget
  have hlen' : Ds.length = H.Fs.length := hlen.trans B.inputs_length
  rw [hw] at hencoded
  change F.R dst = (Ds.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++tail at hencoded
  refine ⟨Ds,hlen',?_,?_⟩
  · simpa only [List.flatMap_def] using hencoded
  · intro r
    have hr : r.val < Ds.length := by rw [hlen']; exact r.isLt
    have hD : ReplicaHaloRowSpec (B.problem htarget) r.val (Ds.getD r.val (fun _ => 0)) := by
      rw [List.getD_eq_getElem _ _ hr]
      exact hrows ⟨r.val,hr⟩
    exact B.accept_row htarget r _ hD

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
