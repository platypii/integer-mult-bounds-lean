module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackClass
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Packed coordinates for the weighted projector action. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine.FlatCoordinateLayout Cover.Fallback Matrix M8.Exchange M8.ReversedExchange
open IntegerMultBounds.Swap.Shear

/-- The split banks of an ordinary row and the residual matrix use the same packed address. -/
theorem ordinaryProjectedRead {m n M W : ℕ} [NeZero M] (dimension : m+m = n)
    (P g : Matrix (Fin m) (Fin m) (ZMod M)) (parent inv : Fin m → ZMod M)
    (input output : Fin (M^(m+m)*W) → ZMod 2)
    (read : ∀ x k,
      let y := transform (diagonal parent) 1 (revExchangeOf (rev m) (g*P*g⁻¹) (transform (diagonal inv) 1 x))
      output (index (Fin.append y.1 y.2) k) = input (index (Fin.append x.1 x.2) k)) :
    let e := finSumFinEquiv.trans (finCongr dimension)
    ∀ x (k : Fin W), output ((index ((projectorResidual e P parent inv g).mulVec x) k).cast (by rw [dimension])) =
      input ((index x k).cast (by rw [dimension])) := by
  subst n
  intro e x k
  let banks := (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
  let y := transform (diagonal parent) 1 (revExchangeOf (rev m) (g*P*g⁻¹) (transform (diagonal inv) 1 banks))
  have append (u v : Fin m → ZMod M) : Sum.elim u v ∘ e.symm = Fin.append u v := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [e]
    | right i =>
      change Sum.elim u v (finSumFinEquiv.symm (Fin.natAdd m i)) = Fin.append u v (Fin.natAdd m i)
      simp only [finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr,Fin.append_right]
  have split : x ∘ e = Sum.elim banks.1 banks.2 := by funext i; cases i <;> rfl
  have joined : Fin.append banks.1 banks.2 = x := by
    rw [← append,← split]; funext i; simp
  have projected : (projectorResidual e P parent inv g).mulVec x = Fin.append y.1 y.2 := by
    change (Cover.Fallback.residual _ _ _ _).submatrix e.symm e.symm *ᵥ x = _
    rw [submatrix_mulVec_equiv,show x ∘ e.symm.symm = Sum.elim banks.1 banks.2 from split,residual_mulVec]
    exact append _ _
  rw [projected]
  change output (index (Fin.append y.1 y.2) k) = input (index x k)
  calc
    _ = input (index (Fin.append banks.1 banks.2) k) := read banks k
    _ = _ := congrArg (fun u => input (index u k)) joined

end IntegerMultBounds.MathlibTM2.M6.BitNode
