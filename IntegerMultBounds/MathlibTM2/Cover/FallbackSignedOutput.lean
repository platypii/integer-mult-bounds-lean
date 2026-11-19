module

public import IntegerMultBounds.MathlibTM2.Cover.Weighted
public import IntegerMultBounds.Machine.FlatCoordinateLayout

/-! Recover the decoded output of a signed pass from its encoded cell action. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine FlatCoordinateLayout
variable {r d M W records : ℕ} [NeZero M]

def signedChildAddress (e : (Fin r ⊕ Fin r) ≃ Fin d) (w inv : Fin r → ZMod M)
    (x : Fin d → ZMod M) : Fin d → ZMod M :=
  let t := Weighted.child r w inv (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
  Sum.elim t.1 t.2 ∘ e.symm

omit [NeZero M] in
theorem signedChildAddress_involutive (e : (Fin r ⊕ Fin r) ≃ Fin d) (w inv : Fin r → ZMod M)
    (units : ∀ i, w i * inv i = 1) : Function.Involutive (signedChildAddress e w inv) := by
  intro x
  funext j
  obtain ⟨i,rfl⟩ := e.surjective j
  cases i with
  | inl i => simp [signedChildAddress,Weighted.child,Function.comp_apply,← mul_assoc,units,(Nat.zero_lt_of_lt i.isLt).ne']
  | inr i =>
    have reverse (i : Fin r) : inv i * w i = 1 := (mul_comm ..).trans (units i)
    simp [signedChildAddress,Weighted.child,Function.comp_apply,← mul_assoc,reverse,(Nat.zero_lt_of_lt i.isLt).ne']

/-- The signed action permutes the record interior and fixes the record number
and suffix. Thus an encoded output word has a decoded witness at every cell. -/
theorem signedChildOutput {α β : Type*} (encode : α → β)
    (e : (Fin r ⊕ Fin r) ≃ Fin d) (w inv : Fin r → ZMod M) (units : ∀ i, w i * inv i = 1)
    (before : Fin (records*(M^d*W)) → α) (out : Fin (records*(M^d*W)) → β)
    (action : ∀ j x k, out (finProdFinEquiv (j,index (signedChildAddress e w inv x) k)) =
      encode (before (finProdFinEquiv (j,index x k)))) :
    ∃ after, out = encode ∘ after ∧ ∀ j x k,
      after (finProdFinEquiv (j,index (signedChildAddress e w inv x) k)) =
        before (finProdFinEquiv (j,index x k)) := by
  let position (j : Fin records) (x : Fin d → ZMod M) (k : Fin W) :=
    finProdFinEquiv (j,index x k)
  let after := fun z : Fin (records*(M^d*W)) =>
    let row := finProdFinEquiv.symm z
    let cell := finProdFinEquiv.symm row.2
    before (position row.1 (signedChildAddress e w inv (coordinates cell.1)) cell.2)
  have read (j x k) : after (position j x k) = before (position j (signedChildAddress e w inv x) k) := by
    simp only [after,position,index,Equiv.symm_apply_apply,coordinates_rank]
  have twice := signedChildAddress_involutive e w inv units
  refine ⟨after,?_,fun j x k => (read j _ k).trans (by rw [twice x])⟩
  funext z
  obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨a,k⟩,rfl⟩ := finProdFinEquiv.surjective t
  let x := coordinates (Q := M) (d := d) a
  have pos : finProdFinEquiv (j,finProdFinEquiv (a,k)) = position j x k := by simp [position,index,x]
  rw [pos,Function.comp_apply,read]
  simpa only [position,twice x] using action j (signedChildAddress e w inv x) k

end IntegerMultBounds.MathlibTM2.Cover.Fallback
