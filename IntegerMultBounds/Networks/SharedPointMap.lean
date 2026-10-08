import IntegerMultBounds.Networks.SharedPointLabels
import IntegerMultBounds.Networks.NeighborCounts
import IntegerMultBounds.Networks.CircuitBits
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! The source/output semantic map of the shared-point pair-exclusion circuit.
Inserting the common point gives an exact bijection of supports; summing its
partial outputs counts every intersection-one source exactly once. -/

namespace IntegerMultBounds.Networks.SharedPointMap

open NeighborCounts Labels SharedPointLabels
variable {h : ℕ}

/-- The pair circuit's ground set omits its fixed common point. -/
abbrev PairAway (c : Fin h) := {P : Finset (Fin h) // P.card = 2 ∧ c ∉ P}

/-- The pair output excludes the other two points of the target triple. -/
abbrev ExcludedPair (c : Fin h) (T : Triple h) :=
  {P : PairAway c // Disjoint P.val (T.val.erase c)}

/-- The corresponding global support consists of intersection exactly `{c}`. -/
abbrev SharedSource (c : Fin h) (T : Triple h) :=
  {S : Triple h // S.val ∩ T.val = {c}}

def insertTriple (c : Fin h) (P : PairAway c) : Triple h :=
  ⟨insert c P.val, by rw [Finset.card_insert_of_notMem P.property.2, P.property.1]⟩

@[simp] theorem insertTriple_common (c : Fin h) (P : PairAway c) : c ∈ (insertTriple c P).val :=
  Finset.mem_insert_self _ _

/-- No pair inputs collapse when inserted into a common-point triple family. -/
theorem insertTriple_injective (c : Fin h) : Function.Injective (insertTriple c) := by
  intro P Q hpq
  apply Subtype.ext
  have he := congrArg (fun S : Triple h => S.val.erase c) hpq
  simpa only [insertTriple, Finset.erase_insert P.property.2, Finset.erase_insert Q.property.2] using he

theorem inserted_intersection (c : Fin h) (T : Triple h) (hc : c ∈ T.val)
    (P : PairAway c) :
    (insertTriple c P).val ∩ T.val = {c} ↔ Disjoint P.val (T.val.erase c) := by
  constructor
  · intro he
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hm : x ∈ (insertTriple c P).val ∩ T.val :=
      Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem hx, (Finset.mem_erase.mp hxt).2⟩
    rw [he, Finset.mem_singleton] at hm
    exact (Finset.mem_erase.mp hxt).1 hm
  · intro hd
    ext x
    simp only [insertTriple, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨he | hx, hxt⟩
      · exact he
      · by_contra hne
        exact Finset.disjoint_left.mp hd hx (Finset.mem_erase.mpr ⟨hne, hxt⟩)
    · rintro rfl
      exact ⟨Or.inl rfl, hc⟩

/-- The exact local-to-global support bijection used by every partial output. -/
def exclusionEquiv (c : Fin h) (T : Triple h) (hc : c ∈ T.val) :
    ExcludedPair c T ≃ SharedSource c T where
  toFun P := ⟨insertTriple c P.val, (inserted_intersection c T hc P.val).mpr P.property⟩
  invFun S := by
    have hcS : c ∈ S.val.val := by
      have hm : c ∈ S.val.val ∩ T.val := by rw [S.property]; simp
      exact (Finset.mem_inter.mp hm).1
    refine ⟨⟨S.val.val.erase c, ?_, Finset.notMem_erase _ _⟩, ?_⟩
    · rw [Finset.card_erase_of_mem hcS, S.val.property]
    · apply Finset.disjoint_left.mpr
      intro x hx hxt
      have hm : x ∈ S.val.val ∩ T.val :=
        Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hx).2, (Finset.mem_erase.mp hxt).2⟩
      rw [S.property, Finset.mem_singleton] at hm
      exact (Finset.mem_erase.mp hx).1 hm
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.erase_insert P.val.property.2
  right_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finset.insert_erase
    have hm : c ∈ S.val.val ∩ T.val := by rw [S.property]; simp
    exact (Finset.mem_inter.mp hm).1

/-- A source cannot occur in two different common-point partial outputs. -/
theorem common_unique (S T : Triple h) (c d : Fin h)
    (hc : S.val ∩ T.val = {c}) (hd : S.val ∩ T.val = {d}) : c = d := by
  have he : ({c} : Finset (Fin h)) = {d} := hc.symm.trans hd
  simpa using he

section Sums
variable {R : Type*} [AddCommMonoid R]

/-- The precise pair-exclusion partial output after remapping pair inputs. -/
def partialOutput (c : Fin h) (T : Triple h) (X : Triple h → R) : R :=
  ∑ P : ExcludedPair c T, X (insertTriple c P.val)

/-- The same output described directly by its global triple support. -/
def sharedOutput (c : Fin h) (T : Triple h) (X : Triple h → R) : R :=
  ∑ S : Triple h, if S.val ∩ T.val = {c} then X S else 0

/-- Insertion/erasure preserves both source identity and multiplicity. -/
theorem partialOutput_eq_shared (c : Fin h) (T : Triple h) (hc : c ∈ T.val)
    (X : Triple h → R) : partialOutput c T X = sharedOutput c T X := by
  calc
    _ = ∑ S : SharedSource c T, X S.val :=
      Fintype.sum_equiv (exclusionEquiv c T hc) _ _ (fun _ => rfl)
    _ = ∑ S : Triple h, if S.val ∩ T.val = {c} then X S else 0 := by
      rw [← Finset.sum_filter]
      symm
      exact Finset.sum_subtype _ (by simp) X

/-- Exactly one partial output contributes each neighboring source. This is
valid in every additive commutative monoid, without cancellation or parity. -/
theorem sum_shared_eq_neighbors (T : Triple h) (X : Triple h → R) :
    (∑ c : {c : Fin h // c ∈ T.val}, sharedOutput c.val T X) =
      ∑ S : Triple h, if BitNeighbor S T then X S else 0 := by
  unfold sharedOutput
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hST : (S.val ∩ T.val).card = 1
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hST
    have hcT : c ∈ T.val := by
      have hm : c ∈ S.val ∩ T.val := by rw [hc]; simp
      exact (Finset.mem_inter.mp hm).2
    have he (d : {d : Fin h // d ∈ T.val}) : S.val ∩ T.val = {d.val} ↔ d = ⟨c, hcT⟩ := by
      constructor
      · intro hd
        apply Subtype.ext
        exact (common_unique S T c d.val hc hd).symm
      · rintro rfl
        exact hc
    simp [he, BitNeighbor, hST]
  · have he (d : {d : Fin h // d ∈ T.val}) : S.val ∩ T.val ≠ {d.val} := by
      intro hd
      apply hST
      rw [hd, Finset.card_singleton]
    simp [he, BitNeighbor, hST]

/-- Summing the three target-associated pair-exclusion outputs is exactly the
existing intersection-one neighbor map, with no duplicate source contribution. -/
theorem sum_partialOutput_eq_neighbors (T : Triple h) (X : Triple h → R) :
    (∑ c : {c : Fin h // c ∈ T.val}, partialOutput c.val T X) =
      ∑ S : Triple h, if BitNeighbor S T then X S else 0 := by
  simp_rw [partialOutput_eq_shared _ T (Subtype.property _)]
  exact sum_shared_eq_neighbors T X
end Sums

/-- The optimized shared-point outputs agree with the existing bit circuit's
copy-then-inject side map under any explicit enumeration of triples and pairs. -/
theorem sum_partialOutput_eq_bit_side {n a : ℕ} (e : Fin n ≃ Triple h)
    (pairs : Fin a ≃ Circuit.BitPair (fun i => (e i).val))
    (X : Triple h → ZMod 2) (i : Fin n) :
    (∑ c : {c : Fin h // c ∈ (e i).val}, partialOutput c.val (e i) X) =
      Circuit.mv (Circuit.bitInject pairs) (Circuit.mv (Circuit.bitCopy pairs) (X ∘ e)) i := by
  rw [sum_partialOutput_eq_neighbors]
  symm
  simp only [Circuit.mv, Function.comp_apply]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, Circuit.bit_side_coeff]
  apply Fintype.sum_equiv e
  intro S
  simp only [BitNeighbor, Finset.inter_comm]
  split_ifs <;> simp

/-- The actual pair-indexed source support of a partial output. -/
def outputSpan (c : Fin h) (T : Triple h) : Submodule ℚ (Fin h → ℚ) :=
  indexedSpan (fun P : PairAway c => (insertTriple c P).val)
    {P | Disjoint P.val (T.val.erase c)}

/-- Shared-point source-span nondegeneracy applies to these exact pair supports. -/
theorem outputSpan_nondegenerate (c : Fin h) (T : Triple h) :
    ((rational h).restrict (outputSpan c T)).Nondegenerate :=
  indexedSpan_nondegenerate c _ _
    (fun P _ => (insertTriple c P).property) (fun P _ => insertTriple_common c P)

/-- Its generators are precisely the shared-point neighboring triples. -/
theorem outputSpan_eq_sourceSpan (c : Fin h) (T : Triple h) (hc : c ∈ T.val) :
    outputSpan c T = sourceSpan {S | S.card = 3 ∧ S ∩ T.val = {c}} := by
  unfold outputSpan indexedSpan
  congr 1
  ext S
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨(insertTriple c P).property, (inserted_intersection c T hc P).mpr hP⟩
  · rintro ⟨hS, hST⟩
    let S' : SharedSource c T := ⟨⟨S, hS⟩, hST⟩
    let P := (exclusionEquiv c T hc).symm S'
    refine ⟨P.val, P.property, ?_⟩
    exact congrArg (fun z : SharedSource c T => z.val.val)
      ((exclusionEquiv c T hc).apply_symm_apply S')

/-- Every partial-output source label is orthogonal to its target line for the
corrected rational form, because its intersection with the target is exactly one. -/
theorem outputSpan_orthogonal (c : Fin h) (T : Triple h) (hc : c ∈ T.val) :
    outputSpan c T ≤ (rational h).orthogonal (ℚ ∙ (indicator T.val : Fin h → ℚ)) := by
  rw [outputSpan_eq_sourceSpan c T hc]
  apply Submodule.span_le.mpr
  rintro x ⟨S, ⟨hS, hST⟩, rfl⟩ y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hi : (T.val ∩ S).card = 1 := by rw [Finset.inter_comm, hST, Finset.card_singleton]
  have hz := rational_neighbors T.val S T.property hS hi
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hz, mul_zero]

/-- Equivalently, the target line enters the orthogonal complement used by the
reverse output frame. -/
theorem target_le_outputSpan_orthogonal (c : Fin h) (T : Triple h) (hc : c ∈ T.val) :
    (ℚ ∙ (indicator T.val : Fin h → ℚ)) ≤ (rational h).orthogonal (outputSpan c T) := by
  intro x hx y hy
  exact (Labels.form_symm (1 / 9) y x).trans (outputSpan_orthogonal c T hc hy x hx)

end IntegerMultBounds.Networks.SharedPointMap
