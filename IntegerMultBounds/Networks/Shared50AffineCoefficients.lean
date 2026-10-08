import IntegerMultBounds.Networks.Shared50AffineControl
import IntegerMultBounds.Networks.Shared50CoefficientMachines

/-! Coefficients of the actual refined scalar schedules. Their denominators
come from the protected rational matrix entries, and actual diagonal scalings
have numerators coprime to the chosen prime. Literal coefficient arithmetic
and the fixed signed numerator/denominator unit recipe therefore require no
new coefficient assumptions. This is not a payload permutation or time theorem. -/

namespace IntegerMultBounds.Networks.Shared50AffineCoefficients

noncomputable section
open Shared50ModularControl (prime)
open Shared50ModularSchedule (Index)
open Shared50AffineControl (rationalSchedules schedules)
open Machine.RadixDigits

/-- A unit rational reduction forces its numerator to avoid the prime. No
numerator magnitude bound is required. -/
theorem numerator_coprime_of_ratMod_unit (q : ℕ) (hq : q.Prime) (r : ℚ)
    (hu : IsUnit (Swap.Modular.ratMod q r)) : r.num.natAbs.Coprime q := by
  let : Fact q.Prime := ⟨hq⟩
  rw [Nat.coprime_comm,hq.coprime_iff_not_dvd]
  intro hdvd
  have hz : (r.num : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd r.num q).mpr (Int.natCast_dvd.mpr hdvd)
  apply hu.ne_zero
  rw [Swap.Modular.ratMod,hz,zero_mul]

/-- Sign separates a signed integer numerator from its fixed positive magnitude. -/
theorem numerator_sign (m : ℕ) (r : ℚ) :
    (r.num : ZMod m) = (if 0 ≤ r.num then 1 else -1) * (r.num.natAbs : ZMod m) := by
  have hh : r.num = (if 0 ≤ r.num then 1 else -1) * (r.num.natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hc := congrArg (fun z : ℤ => (z : ZMod m)) hh
  simpa only [Int.cast_mul,Int.cast_ite,Int.cast_one,Int.cast_neg,Int.cast_natCast] using hc

section Origin
variable {ι : Type*}

def ScalarCoefficient (r : ℚ) : OrderedAffine.Op ι ℚ → Prop
  | .scale _ a => r = a
  | .shift _ _ a => r = a

/-- Cross-group reflected addition has just the two implicit coefficients ±1. -/
def Coefficient (r : ℚ) : AffineFieldProgram.Op ι ℚ → Prop
  | .affineH op => ScalarCoefficient r op
  | .affineD op => ScalarCoefficient r op
  | .addToD _ _ => r = 1
  | .subFromD _ _ => r = 1 ∨ r = -1
  | .interchange _ _ => False

variable [Fintype ι] [LinearOrder ι]

private theorem scalar_origin (E : Matrix ι ι ℚ) (op : OrderedAffine.Op ι ℚ)
    (hop : op ∈ OrderedAffine.program E) {r : ℚ} (hr : ScalarCoefficient r op) :
    ∃ i j, r = E i j := by
  rcases OrderedAffine.coefficient_origin E op hop with ⟨i,rfl⟩ | ⟨i,j,_,rfl⟩
  · exact ⟨i,i,hr⟩
  · exact ⟨i,j,hr⟩

/-- Expanding a field program introduces only entries of its actual transforms
and the already explicit scalar cross-group coefficients. -/
theorem coefficient_origin (p : List (Swap.Shear.Op ι ℚ)) (op : AffineFieldProgram.Op ι ℚ)
    (hop : op ∈ AffineFieldProgram.compile p) {r : ℚ} (hr : Coefficient r op) :
    (r = 1 ∨ r = -1) ∨ ∃ E : Matrix ι ι ℚ,
      (Swap.Shear.Op.transformH E ∈ p ∨ Swap.Shear.Op.transformD E ∈ p) ∧ ∃ i j, r = E i j := by
  obtain ⟨src,hsrc,hin⟩ := List.mem_flatMap.mp hop
  cases src with
  | addToD i j =>
    have hh : op = .addToD i j := by simpa only [AffineFieldProgram.expand,List.mem_singleton] using hin
    subst op
    exact Or.inl (Or.inl hr)
  | subFromD i j =>
    have hh : op = .subFromD i j := by simpa only [AffineFieldProgram.expand,List.mem_singleton] using hin
    subst op
    exact Or.inl hr
  | interchange i j =>
    have hh : op = .interchange i j := by simpa only [AffineFieldProgram.expand,List.mem_singleton] using hin
    subst op
    exact False.elim hr
  | transformH E =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hin
    exact Or.inr ⟨E,Or.inl hsrc,scalar_origin E a ha hr⟩
  | transformD E =>
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hin
    exact Or.inr ⟨E,Or.inr hsrc,scalar_origin E a ha hr⟩

end Origin

/-- Occurrence in the fixed actual scalar schedules, including cross-group ±1. -/
def Occurs (r : ℚ) : Prop :=
  ∃ p ∈ rationalSchedules, ∃ op ∈ p, Coefficient r op

/-- A genuine diagonal scale in one actual refined H/D transform. -/
def ScaleOccurs (r : ℚ) : Prop :=
  ∃ p ∈ rationalSchedules, ∃ i : Index,
    AffineFieldProgram.Op.affineH (.scale i r) ∈ p ∨ AffineFieldProgram.Op.affineD (.scale i r) ∈ p

theorem scale_occurs {r : ℚ} (hr : ScaleOccurs r) : Occurs r := by
  obtain ⟨p,hp,i,hi⟩ := hr
  rcases hi with hi | hi
  · exact ⟨p,hp,_,hi,rfl⟩
  · exact ⟨p,hp,_,hi,rfl⟩

/-- Denominator protection is derived from actual schedule membership. -/
theorem denominator_bound {r : ℚ} (hr : Occurs r) : r.den < prime := by
  obtain ⟨p,hp,op,hop,hcoeff⟩ := hr
  obtain ⟨src,hsrc,rfl⟩ := List.mem_map.mp hp
  rcases coefficient_origin src op hop hcoeff with hunit | ⟨E,hE,i,j,rfl⟩
  · rcases hunit with rfl | rfl <;>
      simpa using (show 1 < prime from lt_trans (by decide) Shared50ModularControl.prime_odd)
  · exact Shared50CoefficientMachines.coefficient_bound E ⟨src,hsrc,hE⟩ i j

/-- The same actual scale remains a unit at the first prime-power width. -/
theorem scale_ratMod_unit {r : ℚ} (hr : ScaleOccurs r) : IsUnit (Swap.Modular.ratMod prime r) := by
  obtain ⟨p,hp,i,hi⟩ := hr
  let mapped := p.map (AffineFieldProgram.mapOp (Swap.Modular.ratMod prime))
  have hm : mapped ∈ schedules prime := by
    rw [Shared50AffineControl.schedules_eq_map]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hl : ∀ op ∈ mapped, AffineFieldProgram.Legal op := by
    have h := Shared50AffineControl.schedules_legal 1
    rw [pow_one] at h
    exact h mapped hm
  rcases hi with hi | hi
  · exact hl _ (List.mem_map.mpr ⟨_,hi,rfl⟩)
  · exact hl _ (List.mem_map.mpr ⟨_,hi,rfl⟩)

theorem scale_numerator_coprime {r : ℚ} (hr : ScaleOccurs r) : r.num.natAbs.Coprime prime :=
  numerator_coprime_of_ratMod_unit prime Shared50ModularControl.prime_prime r (scale_ratMod_unit hr)

local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

/-- Fixed positive integer unit magnitudes and a fixed sign implement every
actual rational scale at all widths, without a bound on numerator size. -/
theorem unit_recipe {r : ℚ} (hr : ScaleOccurs r) (b : ℕ) :
    0 < r.num.natAbs ∧ 0 < r.den ∧
    r.num.natAbs.Coprime (prime ^ b) ∧ r.den.Coprime (prime ^ b) ∧
    ∀ x : ZMod (prime ^ b), Swap.Modular.ratMod (prime ^ b) r * x =
      (if 0 ≤ r.num then 1 else -1) *
        ((r.num.natAbs : ZMod (prime ^ b)) * ((r.den : ZMod (prime ^ b))⁻¹ * x)) := by
  have hn := scale_numerator_coprime hr
  have hpos : 0 < r.num.natAbs := by
    by_contra h
    have hz : r.num.natAbs = 0 := by omega
    rw [hz,Nat.coprime_zero_left] at hn
    have hp := Shared50ModularControl.prime_odd
    omega
  refine ⟨hpos,r.den_pos,hn.pow_right b,
    Machine.RadixRational.denominator_coprime r (denominator_bound (scale_occurs hr)) b,?_⟩
  intro x
  rw [Swap.Modular.ratMod,numerator_sign]
  ring

/-- Exact literal arithmetic for every actual affine coefficient; the denominator
condition is discharged by the schedule rather than supplied by the caller. -/
theorem coefficient_to_blank (r : ℚ) (hr : Occurs r) (xs : List (Fin prime)) :
    let result := Machine.RadixRationalData.digits (Machine.RadixRationalData.initial r.num r.den) xs
    let finalCarry := Machine.RadixRationalData.overflow (Machine.RadixRationalData.initial r.num r.den) xs
    (value result : ZMod (prime ^ xs.length)) =
      Swap.Modular.ratMod (prime ^ xs.length) r * (value xs : ZMod (prime ^ xs.length)) ∧
    result.length = xs.length ∧
    Machine.run (Shared50CoefficientMachines.coefficientProgram r) xs.length
      (Machine.RadixRational.cfg (Machine.wordTape (xs.map digitSymbol)) (fun _ => Machine.blank)
        0 0 (Machine.RadixRationalData.initial r.num r.den)) =
      some (Machine.RadixRational.cfg (Machine.wordTape (xs.map digitSymbol))
        (Machine.wordTape (result.map digitSymbol)) xs.length xs.length finalCarry) ∧
    Machine.step (Shared50CoefficientMachines.coefficientProgram r)
      (Machine.RadixRational.cfg (Machine.wordTape (xs.map digitSymbol))
        (Machine.wordTape (result.map digitSymbol)) xs.length xs.length finalCarry) = none :=
  Machine.RadixRational.rational_to_blank r (denominator_bound hr) xs

end
end IntegerMultBounds.Networks.Shared50AffineCoefficients
