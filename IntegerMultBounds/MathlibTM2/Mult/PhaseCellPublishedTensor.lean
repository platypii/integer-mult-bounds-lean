module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedOperator
public import IntegerMultBounds.NLogN.TensorApproxD

/-! Published line maps compose through the existing tensor theorem. The only
dimension factor is the sum of coordinate errors; window counts do not enter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN

theorem publishedWindows_tensor_spec (p d : ℕ) (N : Fin d → ℕ) [∀ i, NeZero (N i)]
    (A : (i : Fin d) → (ZMod (N i) → ℂ) →L[ℂ] (ZMod (N i) → ℂ))
    (ws : (i : Fin d) → List (Window (ZMod (N i))))
    (localOut : (i : Fin d) → Window (ZMod (N i)) → (ZMod (N i) → ℂ) → ZMod (N i) → ℂ)
    (initial : (i : Fin d) → (ZMod (N i) → ℂ) → ZMod (N i) → ℂ)
    (error : Fin d → ℝ) (he : ∀ i, 0 ≤ error i)
    (hcover : ∀ i j, ∃ w ∈ ws i, j ∈ w.core)
    (hlocal : ∀ i w, w ∈ ws i → ∀ u, ‖u‖ ≤ 1 →
      ErrorOn w.core (localOut i w u) (A i u) (error i/2^p))
    (hA : ∀ i, ‖A i‖ ≤ 1/2) (hsmall : ∀ i, error i/2^p ≤ 1/2) :
    let compute := fun i u => publishWindows (fun w => localOut i w u) (ws i) (initial i u)
    ApproxMap p (tensorD d N compute) (tensorDCLM d N A) (∑ i, error i) ∧
      ∀ u, ‖u‖ ≤ 1 → ‖tensorD d N compute u‖ ≤ 1 := by
  dsimp only
  have hline (i : Fin d) := publishedWindows_operator_spec p (A i) (ws i) (localOut i)
    (initial i) (error i) (he i) (hcover i) (hlocal i) (hA i) (hsmall i)
  exact ⟨approxMap_tensorD d N _ A error (fun i => (hA i).trans (by norm_num))
    (fun i => (hline i).1) (fun i => (hline i).2),
    tensorD_ball d N _ (fun i => (hline i).2)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
