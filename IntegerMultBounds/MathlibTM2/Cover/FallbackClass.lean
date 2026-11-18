module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignStream
public import IntegerMultBounds.MathlibTM2.Cover.LabelProjector

/-! Residue table of a weighted reversed projector at its physical label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section
open Matrix M8.ReversedExchange
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_odd)
open IntegerMultBounds.Swap.Modular (reduce Admissible reduce_mul)
variable {m n w : ℕ}
local instance : Fact prime.Prime := ⟨IntegerMultBounds.Networks.Shared50ModularControl.prime_prime⟩

def projectorResidual {R : Type*} [CommRing R] (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (P : Matrix (Fin m) (Fin m) R) (α α' : Fin m → R) (g : Matrix (Fin m) (Fin m) R) :=
  reindex e e (residual (diagonal α) (diagonal α') (rev m) (g * P * g⁻¹))

private theorem residual_map {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (φ : R →+* S) (A B C P : Matrix ι ι R) :
    φ.mapMatrix (residual A B C P) =
      residual (φ.mapMatrix A) (φ.mapMatrix B) (φ.mapMatrix C) (φ.mapMatrix P) := by
  have block (a b c d : Matrix ι ι R) : φ.mapMatrix (fromBlocks a b c d) =
      fromBlocks (φ.mapMatrix a) (φ.mapMatrix b) (φ.mapMatrix c) (φ.mapMatrix d) :=
    fromBlocks_map ..
  simp only [residual,map_mul,block,map_zero,map_sub,map_one]

theorem projectorResidual_class (hw : 0 < w) (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (P : Matrix (Fin m) (Fin m) ℚ) (adm : Admissible prime P)
    (α α' : Fin m → ZMod (prime^w)) (g : LabelPadding.Label m w) (hg : IsUnit g.det) :
    let φ := LabelRing.res prime w hw
    φ.mapMatrix (projectorResidual e (reduce (prime^w) P) α α' g) =
      projectorResidual e (reduce prime P) (φ ∘ α) (φ ∘ α') (φ.mapMatrix g) := by
  intro φ
  unfold projectorResidual
  have commute (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod (prime^w))) :
      φ.mapMatrix (reindex e e X) = reindex e e (φ.mapMatrix X) := rfl
  rw [commute]
  rw [residual_map,LabelRing.res_conj prime w hw _ _ hg,LabelProjector.residue_reduce hw P adm]
  have diag (a : Fin m → ZMod (prime^w)) : φ.mapMatrix (diagonal a) = diagonal (φ ∘ a) := by
    ext i j
    by_cases h : i = j <;> simp [h,diagonal]
  have flip : φ.mapMatrix (rev m) = rev m := by
    ext i j
    by_cases h : j = i.rev <;> simp [rev,h]
  rw [diag,diag,flip]

theorem projectorResidual_sign (hw : 0 < w) (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (P : LabelPadding.Label m w) (hp : P * P = P)
    (α α' : Fin m → ZMod (prime^w)) (ha : ∀ i, α i * α' i = 1)
    (g : LabelPadding.Label m w) (hg : IsUnit g.det) :
    let G := projectorResidual e P α α' g
    G.det = 1 ∨ G.det = -1 := by
  have idem : (g*P*g⁻¹)*(g*P*g⁻¹) = g*P*g⁻¹ := by
    calc
      _ = g*(P*(g⁻¹*g)*P)*g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [nonsing_inv_mul g hg,Matrix.mul_one,hp]
  simpa only [projectorResidual,det_reindex_self] using
    residual_det_sign prime_odd hw (diagonal α) (diagonal α') (rev m) (g*P*g⁻¹)
      (by simp [diagonal_mul_diagonal,ha,diagonal_one])
      (by simp [diagonal_mul_diagonal,mul_comm,ha,diagonal_one])
      rev_mul_rev idem

/-- Given the residue weights, the projector table supplies the sign in the stream
at the addressed live label for every compatible lift of the weights. -/
theorem projectorSign_at {A : ℕ} (hw : 0 < w) (e : (Fin m ⊕ Fin m) ≃ Fin n)
    (P : Matrix (Fin m) (Fin m) ℚ) (hp : P*P = P) (adm : Admissible prime P)
    (α α' : Fin m → ZMod (prime^w)) (ha : ∀ i, α i * α' i = 1)
    (g : LabelPadding.Label m w) (hg : IsUnit g.det) (p N : ℕ)
    (index : p*(prime^w)^(m*m)+(LabelAddress.address g).val < N) :
    let φ := LabelRing.res prime w hw
    let table := projectorResidual e (reduce prime P) (φ ∘ α) (φ ∘ α')
    let G := projectorResidual e (reduce (prime^w) P) α α' g
    let pivots := classPivots (table (φ.mapMatrix g))
    let j := p*(prime^w)^(m*m)+(LabelAddress.address g).val
    ∃ negative, (signStream (A := A) table w N)[j]? = some (bitSymbol negative) ∧
      Itinerary.Valid pivots G n ∧ (Itinerary.run pivots G n).det = if negative then -1 else 1 := by
  have liftAdm : Admissible (prime^w) P := fun i j => (adm i j).pow_right w
  have idem : reduce (prime^w) P * reduce (prime^w) P = reduce (prime^w) P := by
    rw [← reduce_mul _ liftAdm liftAdm,hp]
  exact signStream_at _ hw g _ p N (projectorResidual_sign hw e _ idem α α' ha g hg)
    (projectorResidual_class hw e P adm α α' g hg) index

end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
