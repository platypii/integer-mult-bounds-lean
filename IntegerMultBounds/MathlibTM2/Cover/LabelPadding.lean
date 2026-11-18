module

public import IntegerMultBounds.MathlibTM2.Cover.BadClass
public import Mathlib.GroupTheory.Index
public import IntegerMultBounds.MathlibTM2.Cover.LabelRing
public import IntegerMultBounds.MathlibTM2.Cover.LabelPermutation
public import IntegerMultBounds.MathlibTM2.Cover.LabelEntry

/-! A payload on invertible labels extends by zero to the physical matrix box. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelPadding
noncomputable section

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor index)
open LabelEntry (Cell)
variable {m w B : ℕ} {v : Descriptor}
local instance : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

abbrev Label (m w : ℕ) := Matrix (Fin m) (Fin m) (ZMod (prime^w))

/-- Read one bit of the record stored at a label. -/
def read (x : ℕ → ZMod 2) (g : Label m w) (z : Cell v B) :=
  x (index prime v z.a z.row (z.b.val*prime^(m*(w*m))+(LabelAddress.address g).val)
    z.h z.mid z.d z.after)

/-- A singular residue class contains only padding. -/
def Padded (m w : ℕ) (v : Descriptor) (B : ℕ) (x : ℕ → ZMod 2) :=
  ∀ (g : Label m w), ¬IsUnit g → ∀ z : Cell v B, read x g z = 0

theorem singular_iff (hw : 0 < w) (g : Label m w) :
    ¬IsUnit g ↔ ((LabelRing.res prime w hw).mapMatrix g).det = 0 := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  rw [Matrix.isUnit_iff_isUnit_det, LabelRing.isUnit_iff_res prime w hw,
    RingHom.map_det, not_not]

open Finset in
open scoped Classical in
/-- The fraction of padding in the whole runtime box equals the singular fraction
in the residue field, so the same bound holds at every positive width. -/
theorem padding_count (hw : 0 < w) :
    #{g : Label m w | ¬IsUnit g} * prime ≤ m * Fintype.card (Label m w) := by
  classical
  let : Fact prime.Prime := ⟨prime_prime⟩
  let low := Matrix (Fin m) (Fin m) (ZMod prime)
  let f : Label m w →+ low := (LabelRing.res prime w hw).mapMatrix.toAddMonoidHom
  have onto : Function.Surjective f := by
    intro g
    choose a ha using (fun i j => ZMod.castHom_surjective (dvd_pow_self prime hw.ne') (g i j))
    exact ⟨a, funext fun i => funext fun j => ha i j⟩
  let n := #{g : Label m w | f g = 0}
  have fibers (g : low) : #{a : Label m w | f a = g} = n :=
    AddMonoidHom.card_fiber_eq_of_mem_range f (onto g) (onto 0)
  have count (s : Finset low) : #{g : Label m w | f g ∈ s} = s.card * n := by
    rw [← sum_card_fiberwise_eq_card_filter]
    simp [fibers]
  have total := count univ
  simp only [mem_univ, filter_true, card_univ] at total
  have bad := count {g : low | g.det = 0}
  simp only [mem_filter, mem_univ, true_and] at bad
  have h := BadClass.singular_count (F := ZMod prime) (m := m)
  rw [ZMod.card] at h
  have cards : Fintype.card low = prime^(m*m) := by
    simp [low, Matrix, ← pow_mul]
  simp only [singular_iff hw]
  change #{g : Label m w | (f g).det = 0} * prime ≤ _
  rw [bad, total, cards]
  rw [Nat.mul_right_comm _ n prime, ← Nat.mul_assoc m]
  apply Nat.mul_le_mul_right
  convert h using 2
  congr 1
  ext g
  simp

/-- A route preserves zero padding in both directions, at every spectator and payload position. -/
theorem transport {x y : ℕ → ZMod 2} {σ : Label m w} (hu : IsUnit σ)
    (hr : LabelPermutation.Transport v B w (fun g => g * σ) x y) :
    Padded m w v B x ↔ Padded m w v B y := by
  obtain ⟨u, rfl⟩ := hu
  have h (g : Label m w) (z : Cell v B) : read y (g * (↑u : Label m w)) z = read x g z :=
    hr g _ z.a.isLt _ z.row.isLt _ z.b.isLt _ z.h.isLt _ z.mid.isLt _ z.d.isLt _ z.after.isLt
  constructor
  · intro hx g hg z
    have hinv := h (g * (↑u⁻¹ : Label m w)) z
    simp only [Matrix.mul_assoc, Units.inv_mul, mul_one] at hinv
    exact hinv.trans (hx _ (fun hg' => hg (by simpa [mul_assoc] using hg'.mul u.isUnit)) z)
  · intro hy g hg z
    exact (h g z).symm.trans (hy _ (fun hg' => hg (by simpa [mul_assoc] using hg'.mul (u⁻¹).isUnit)) z)

end
end IntegerMultBounds.MathlibTM2.Cover.LabelPadding
