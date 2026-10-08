import IntegerMultBounds.Networks.Shared50FiniteInterchange
import IntegerMultBounds.Machine.RadixRational

/-! Literal coefficient machines for the actual fixed rational control lists.
All coefficient denominators are certified by the already chosen schedule
prime; no extra denominator or implementation contract is assumed. These are
individual arithmetic kernels, not yet a tape implementation of a matrix sweep. -/

namespace IntegerMultBounds.Networks.Shared50CoefficientMachines

noncomputable section
open Swap.Shear
open ModularFrameSchedule
open Shared50ModularSchedule (Index)
open Shared50ModularControl (prime)
open Shared50FiniteInterchange (rationalFieldPrograms)
open Machine.RadixDigits

section Generic
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Every coefficient of a whole-group transform has a denominator below Q. -/
def CoeffBound (Q : ℕ) : Op ι ℚ → Prop
  | .transformH E => ∀ i j, (E i j).den < Q
  | .transformD E => ∀ i j, (E i j).den < Q
  | _ => True

omit [LinearOrder ι] in
private theorem coefficient_mem (E : Matrix ι ι ℚ) (i j : ι) :
    (E i j).den ∈ Swap.Modular.denominators E := by
  classical
  exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩

omit [Fintype ι] [LinearOrder ι] in
private theorem pivots_bound (Q : ℕ) (L : List (ι × ι)) :
    ∀ op ∈ pivotsProgram (R := ℚ) L, CoeffBound Q op := by
  induction L with
  | nil => simp [pivotsProgram]
  | cons p rest ih => simpa [pivotsProgram,pivotProgram,CoeffBound] using ih

/-- Factor coefficients belong to the very denominator set used to choose the prime. -/
theorem rational_program_bound (Q : ℕ) (e : Edge ι)
    (hd : ∀ d ∈ edgeDenominators e, d < Q) :
    ∀ op ∈ ModularProgramShape.rationalProgram e, CoeffBound Q op := by
  have hf : ∀ E ∈ [(factors e).E₁,(factors e).E₁',(factors e).E₂,(factors e).E₂'],
      ∀ i j, (E i j).den < Q := by
    intro E hE i j
    apply hd
    apply Finset.mem_union_right
    have hc := coefficient_mem E i j
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ hc)))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hc))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
    · exact Finset.mem_union_right _ hc
  intro op hop
  simp only [ModularProgramShape.rationalProgram,shearProgram,List.mem_append,List.mem_cons,
    List.not_mem_nil,or_false] at hop
  rcases hop with (h | h) | h
  · rcases h with rfl | rfl
    · exact hf _ (by simp)
    · exact hf _ (by simp)
  · exact pivots_bound Q _ op h
  · rcases h with rfl | rfl
    · exact hf _ (by simp)
    · exact hf _ (by simp)

omit [LinearOrder ι] in
private theorem post_bound (Q : ℕ) :
    ∀ op ∈ Shared50FiniteInterchange.postFields (ι := ι) (R := ℚ), CoeffBound Q op := by
  intro op hop
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hop
  trivial

private theorem pre_bound (Q : ℕ) (hQ : 1 < Q) :
    ∀ op ∈ Shared50FiniteInterchange.preFields (ι := ι) (R := ℚ), CoeffBound Q op := by
  intro op hop
  simp only [Shared50FiniteInterchange.preFields,List.mem_append,List.mem_singleton] at hop
  rcases hop with h | rfl
  · exact post_bound Q op h
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa using hQ
    · simpa [Matrix.one_apply,hij] using hQ

end Generic

/-- Every transform in the actual complete interchange has protected coefficients,
including the surrounding negative-identity transform. -/
theorem actual_coefficients : ∀ p ∈ rationalFieldPrograms, ∀ op ∈ p, CoeffBound prime op := by
  intro p hp
  simp only [rationalFieldPrograms,List.mem_append] at hp
  rcases hp with (hp | hp) | hp
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact pre_bound prime (by have hh := Shared50ModularControl.prime_odd; omega)
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact rational_program_bound prime e (Shared50ModularControl.edge_bound Shared50ModularControl.prime_bound he)
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hp
    exact post_bound prime

/-- Membership in an actual transform, as opposed to an arbitrary rational matrix. -/
def Occurs (A : Matrix Index Index ℚ) : Prop :=
  ∃ p ∈ rationalFieldPrograms, Op.transformH A ∈ p ∨ Op.transformD A ∈ p

theorem coefficient_bound (A : Matrix Index Index ℚ) (hA : Occurs A) (i j : Index) :
    (A i j).den < prime := by
  obtain ⟨p,hp,hA⟩ := hA
  rcases hA with h | h
  · exact actual_coefficients p hp _ h i j
  · exact actual_coefficients p hp _ h i j

local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

/-- A single coefficient chooses a fixed finite two-tape program, independent of width. -/
def coefficientProgram (r : ℚ) : Machine.Program 2 (2 * r.num.natAbs + r.den + 1) prime :=
  Machine.RadixRational.program prime r.num r.den

/-- The kernel output matches the entry of the actual reduced matrix. -/
theorem output_reducedEntry (A : Matrix Index Index ℚ) (hA : Occurs A) (i j : Index)
    (xs : List (Fin prime)) :
    (value (Machine.RadixRationalData.digits (Machine.RadixRationalData.initial (A i j).num (A i j).den) xs) :
        ZMod (prime ^ xs.length)) =
      Swap.Modular.reduce (prime ^ xs.length) A i j * (value xs : ZMod (prime ^ xs.length)) :=
  Machine.RadixRational.output_ratMod (A i j) (coefficient_bound A hA i j) xs

/-- The same actual coefficient contract holds on arbitrary tape backgrounds
and head offsets, with only the specified output interval overwritten. -/
theorem coefficient_hoare (A : Matrix Index Index ℚ) (hA : Occurs A) (i j : Index)
    (xs : List (Fin prime)) (source out : ℤ → Fin (prime + 4)) (p t : ℤ)
    (hf : source (p + xs.length) = Machine.blank) :
    Machine.HoareTime (coefficientProgram (A i j))
      (fun v => v = (Machine.RadixRational.cfg (Machine.putWord source p (xs.map digitSymbol)) out p t
        (Machine.RadixRationalData.initial (A i j).num (A i j).den)).tapes)
      (fun v => ∃ result : List (Fin prime),
        (value result : ZMod (prime ^ xs.length)) =
          Swap.Modular.reduce (prime ^ xs.length) A i j * (value xs : ZMod (prime ^ xs.length)) ∧
        result.length = xs.length ∧ v =
          (Machine.RadixRational.cfg (Machine.putWord source p (xs.map digitSymbol))
            (Machine.putWord out t (result.map digitSymbol)) (p + xs.length) (t + xs.length)
            (Machine.RadixRationalData.initial (A i j).num (A i j).den)).tapes)
      xs.length :=
  Machine.RadixRational.rational_hoare (A i j) (coefficient_bound A hA i j) xs source out p t hf

/-- Exact width, genuine halt, whole-source preservation, and the actual matrix
coefficient semantics for every transform in the fixed complete interchange. -/
theorem coefficient_to_blank (A : Matrix Index Index ℚ) (hA : Occurs A) (i j : Index)
    (xs : List (Fin prime)) :
    let r := A i j
    let result := Machine.RadixRationalData.digits (Machine.RadixRationalData.initial r.num r.den) xs
    let finalCarry := Machine.RadixRationalData.overflow (Machine.RadixRationalData.initial r.num r.den) xs
    (value result : ZMod (prime ^ xs.length)) =
      Swap.Modular.reduce (prime ^ xs.length) A i j * (value xs : ZMod (prime ^ xs.length)) ∧
    result.length = xs.length ∧
    Machine.run (coefficientProgram r) xs.length
      (Machine.RadixRational.cfg (Machine.wordTape (xs.map digitSymbol)) (fun _ => Machine.blank)
        0 0 (Machine.RadixRationalData.initial r.num r.den)) =
      some (Machine.RadixRational.cfg (Machine.wordTape (xs.map digitSymbol))
        (Machine.wordTape (result.map digitSymbol)) xs.length xs.length finalCarry) ∧
    Machine.step (coefficientProgram r)
      (Machine.RadixRational.cfg (Machine.wordTape (xs.map digitSymbol))
        (Machine.wordTape (result.map digitSymbol)) xs.length xs.length finalCarry) = none :=
  Machine.RadixRational.rational_to_blank (A i j) (coefficient_bound A hA i j) xs

end
end IntegerMultBounds.Networks.Shared50CoefficientMachines
