module

public import IntegerMultBounds.MathlibTM2.Cover.Itinerary
public import Mathlib.Data.ZMod.Basic

/-!
# The label ring `Z/q^w` and its residue class

Labels have entries in `Z/q^w`. The class of a label is its image in `F_q`, read from the low
digit of each entry (`res`).

* `isLocalRing`: `Z/q^w` is local, so the fallback elimination applies (`exists_itinerary`).
* `isUnit_iff_res`: an entry is a unit exactly when its residue is nonzero.
* `valid_res`: labels in one class have the same valid pivot itineraries.
* `lead_unit_iff`, `res_conj`: whether the leading minors of `g P g⁻¹` are units depends only on
  the class of `g`. So the good/bad branch is a function of the low digits.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelRing

open Matrix
open IntegerMultBounds.MathlibTM2.Cover.GoodForm (lead)

variable (q w : ℕ) [hq : Fact q.Prime]

theorem isUnit_iff (hw : 0 < w) (a : ZMod (q ^ w)) : IsUnit a ↔ ¬ q ∣ a.val := by
  have : NeZero (q ^ w) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact ZMod.isUnit_natCast_iff_not_dvd_pow hq.out hw

theorem isLocalRing (hw : 0 < w) : IsLocalRing (ZMod (q ^ w)) := by
  have : Fact (1 < q ^ w) := ⟨Nat.one_lt_pow hw.ne' hq.out.one_lt⟩
  have : NeZero (q ^ w) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff, isUnit_iff q w hw, not_not] at ha hb
  have hab : a + b = ((a.val + b.val : ℕ) : ZMod (q ^ w)) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [mem_nonunits_iff, hab, ZMod.isUnit_natCast_iff_not_dvd_pow hq.out hw, not_not]
  exact dvd_add ha hb

/-- The residue class of an entry: its low digit. -/
def res (hw : 0 < w) : ZMod (q ^ w) →+* ZMod q :=
  ZMod.castHom (dvd_pow_self q hw.ne') (ZMod q)

theorem res_eq_zero_iff (hw : 0 < w) (a : ZMod (q ^ w)) : res q w hw a = 0 ↔ q ∣ a.val := by
  have : NeZero (q ^ w) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  rw [res, ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]

theorem isUnit_iff_res (hw : 0 < w) (a : ZMod (q ^ w)) : IsUnit a ↔ res q w hw a ≠ 0 := by
  rw [isUnit_iff q w hw, Ne, res_eq_zero_iff]

/-- Labels in one class have the same valid pivot itineraries. -/
theorem valid_res (hw : 0 < w) {n : ℕ} (p : Fin n → Fin n)
    {G G' : Matrix (Fin n) (Fin n) (ZMod (q ^ w))}
    (h : (res q w hw).mapMatrix G = (res q w hw).mapMatrix G') (k : ℕ) :
    Itinerary.Valid p G k ↔ Itinerary.Valid p G' k :=
  Itinerary.valid_congr (res q w hw) (fun a ha => (isUnit_iff_res q w hw a).mpr ha.ne_zero) p h k

/-- A leading minor is a unit exactly when the leading minor of the class is nonzero. -/
theorem lead_unit_iff (hw : 0 < w) {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (G : Matrix (Fin m) (Fin m) (ZMod (q ^ w))) :
    IsUnit (lead k hk G).det ↔ (lead k hk ((res q w hw).mapMatrix G)).det ≠ 0 := by
  rw [isUnit_iff_res q w hw, RingHom.map_det]
  rfl

omit hq in
/-- The class of a conjugated projector is the conjugate by the class. -/
theorem res_conj (hw : 0 < w) {m : ℕ} (g P : Matrix (Fin m) (Fin m) (ZMod (q ^ w)))
    (hg : IsUnit g.det) :
    (res q w hw).mapMatrix (g * P * g⁻¹) =
      (res q w hw).mapMatrix g * (res q w hw).mapMatrix P * ((res q w hw).mapMatrix g)⁻¹ := by
  have hinv : ((res q w hw).mapMatrix g)⁻¹ = (res q w hw).mapMatrix g⁻¹ :=
    Matrix.inv_eq_right_inv (by rw [← map_mul, Matrix.mul_nonsing_inv g hg, map_one])
  rw [hinv, map_mul, map_mul]

/-- **The branch reads only the class.** Two invertible labels in one class have the same
unit leading minors of `g P g⁻¹`. -/
theorem good_congr (hw : 0 < w) {m : ℕ} (P g g' : Matrix (Fin m) (Fin m) (ZMod (q ^ w)))
    (hg : IsUnit g.det) (hg' : IsUnit g'.det)
    (h : (res q w hw).mapMatrix g = (res q w hw).mapMatrix g') (k : ℕ) (hk : k ≤ m) :
    IsUnit (lead k hk (g * P * g⁻¹)).det ↔ IsUnit (lead k hk (g' * P * g'⁻¹)).det := by
  rw [lead_unit_iff q w hw, lead_unit_iff q w hw, res_conj q w hw g P hg,
    res_conj q w hw g' P hg', h]

end IntegerMultBounds.MathlibTM2.Cover.LabelRing
