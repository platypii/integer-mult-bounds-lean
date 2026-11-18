module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackClass

/-! Recover the projector and its residue-table entry at a physical record index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open IntegerMultBounds.Machine.FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open IntegerMultBounds.Swap.Modular (reduce Admissible)
variable {m w n : ℕ}
local notation "M" => prime^w
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def physicalLabel (m w j : ℕ) : LabelPadding.Label m w :=
  let addr : Fin ((prime^w)^(m*m)) := ⟨j % _, Nat.mod_lt _ (pow_pos (pow_pos prime_prime.pos _) _)⟩
  fun r c => coordinates addr (finProdFinEquiv (c,r))

theorem physicalLabel_index (j : ℕ) :
    j / M^(m*m) * M^(m*m) + (LabelAddress.address (physicalLabel m w j)).val = j := by
  let addr : Fin (M^(m*m)) := ⟨j % _, Nat.mod_lt _ (pow_pos (pow_pos prime_prime.pos _) _)⟩
  have digits : M8.AtomOps.refine (Route.cols (physicalLabel m w j)) = coordinates addr := by
    funext i
    simp [M8.AtomOps.refine, Route.cols, physicalLabel, addr]
    exact congrArg (coordinates addr) (finProdFinEquiv.apply_symm_apply i)
  rw [LabelAddress.address,digits,rank_coordinates,Nat.mul_comm]
  exact Nat.div_add_mod ..

theorem physicalLabel_residue (hw : 0 < w) (j : ℕ) :
    LabelStock.residue m w 1 j = (LabelRing.res prime w hw).mapMatrix (physicalLabel m w j) := by
  simpa only [Nat.mul_one,Nat.add_zero,physicalLabel_index] using
    LabelStock.residue_at hw (j / M^(m*m)) 1 0 (by decide) (physicalLabel m w j)

theorem physicalLabel_live (hw : 0 < w) (j : ℕ) :
    LabelStock.live m w 1 j = true ↔ IsUnit (physicalLabel m w j) := by
  simp only [LabelStock.live,decide_eq_true_eq,physicalLabel_residue hw]
  exact (not_congr (LabelPadding.singular_iff hw _)).symm.trans (by simp)

theorem physicalProjector_spec (hw : 0 < w) (j : ℕ) (live : LabelStock.live m w 1 j = true)
    (e : (Fin m ⊕ Fin m) ≃ Fin n) (P : Matrix (Fin m) (Fin m) ℚ) (hp : P*P = P)
    (adm : Admissible prime P) (α α' : Fin m → ZMod M) (ha : ∀ i, α i * α' i = 1) :
    let g := physicalLabel m w j
    let φ := LabelRing.res prime w hw
    let G := projectorResidual e (reduce M P) α α' g
    (G.det = 1 ∨ G.det = -1) ∧ φ.mapMatrix G =
      projectorResidual e (reduce prime P) (φ ∘ α) (φ ∘ α') (LabelStock.residue m w 1 j) := by
  intro g φ G
  have unit := (physicalLabel_live hw j).mp live
  have det := (Matrix.isUnit_iff_isUnit_det _).mp unit
  have liftAdm : Admissible M P := fun r c => (adm r c).pow_right w
  exact ⟨projectorResidual_sign hw e _ (by rw [← IntegerMultBounds.Swap.Modular.reduce_mul _ liftAdm liftAdm,hp]) α α' ha g det,
    by rw [physicalLabel_residue hw]; exact projectorResidual_class hw e P adm α α' g det⟩

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
