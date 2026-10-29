module

public import IntegerMultBounds.NLogN.PhaseCellCoreDescriptors
public import IntegerMultBounds.NLogN.PhaseCellCoreGather
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Arithmetic groups retain ambient endpoint keys. Movement length alone is
insufficient for setup reuse. Fibres account for every owned core exactly once. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellMatrix
open Finset
open scoped BigOperators

def coreSetupKeys (s width band n : ℕ) : Finset (ℕ × ℕ) :=
  (coreIndices s width).toFinset.image (fun k => coreHaloEndpoints s width k band n)

def coreSetupGroup (s width band n : ℕ) (key : ℕ × ℕ) : List ℕ :=
  (coreIndices s width).filter (fun k => decide (coreHaloEndpoints s width k band n = key))

@[simp] theorem mem_coreSetupGroup (s width band n k : ℕ) (key : ℕ × ℕ) :
    k ∈ coreSetupGroup s width band n key ↔
      k ∈ coreIndices s width ∧ coreHaloEndpoints s width k band n = key := by
  simp [coreSetupGroup]

theorem coreSetupGroup_nodup (s width band n : ℕ) (key : ℕ × ℕ) :
    (coreSetupGroup s width band n key).Nodup :=
  (coreIndices_nodup s width).filter _

theorem coreSetupGroup_cover (s width band n k : ℕ) (hk : k ∈ coreIndices s width) :
    ∃ key ∈ coreSetupKeys s width band n, k ∈ coreSetupGroup s width band n key := by
  refine ⟨coreHaloEndpoints s width k band n,?_,?_⟩
  · exact Finset.mem_image_of_mem _ (List.mem_toFinset.mpr hk)
  · exact (mem_coreSetupGroup _ _ _ _ _ _).mpr ⟨hk,rfl⟩

theorem coreSetupGroup_unique (s width band n k : ℕ) (key key' : ℕ × ℕ)
    (hk : k ∈ coreSetupGroup s width band n key) (hk' : k ∈ coreSetupGroup s width band n key') :
    key = key' :=
  ((mem_coreSetupGroup _ _ _ _ _ _).mp hk).2.symm.trans
    ((mem_coreSetupGroup _ _ _ _ _ _).mp hk').2

/-- A non-full endpoint key forces the fitting branch of the halo selector. -/
theorem coreHaloEndpoints_fits_of_ne_full (s width k band n : ℕ)
    (hne : coreHaloEndpoints s width k band n ≠ (0,s)) :
    n*band ≤ coreStart width k ∧ coreStart width k+coreLength s width k+n*band ≤ s := by
  by_contra h
  exact hne (by simp [coreHaloEndpoints,h])

theorem coreHaloEndpoints_injective_of_ne_full (s width i j band n : ℕ) (hw : 0 < width)
    (hne : coreHaloEndpoints s width i band n ≠ (0,s))
    (he : coreHaloEndpoints s width i band n = coreHaloEndpoints s width j band n) : i = j := by
  have hi := coreHaloEndpoints_fits_of_ne_full s width i band n hne
  have hj := coreHaloEndpoints_fits_of_ne_full s width j band n (by rw [← he]; exact hne)
  have ho := congrArg Prod.fst he
  simp only [coreHaloEndpoints,if_pos hi,if_pos hj] at ho
  have hm : i*width = j*width := by dsimp [coreStart] at hi hj ho; omega
  exact Nat.eq_of_mul_eq_mul_right hw hm

/-- The repeated seam fallbacks share the full-system setup. Every other setup
key owns at most one core, though it can still serve many input replicas. -/
theorem coreSetupGroup_subsingleton (s width band n : ℕ) (hw : 0 < width)
    (key : ℕ × ℕ) (hne : key ≠ (0,s)) :
    ∀ i ∈ coreSetupGroup s width band n key, ∀ j ∈ coreSetupGroup s width band n key, i = j := by
  intro i hi j hj
  have hi' := ((mem_coreSetupGroup _ _ _ _ _ _).mp hi).2
  have hj' := ((mem_coreSetupGroup _ _ _ _ _ _).mp hj).2
  exact coreHaloEndpoints_injective_of_ne_full s width i j band n hw
    (by rw [hi']; exact hne) (hi'.trans hj'.symm)

/-- Arithmetic regrouping does not duplicate the per-core solve or publication
bill. This is a ledger identity; physical reordering is a separate tape cost. -/
theorem coreSetupGroup_sum {M : Type*} [AddCommMonoid M]
    (s width band n : ℕ) (f : ℕ → M) :
    (∑ key ∈ coreSetupKeys s width band n,
      ∑ k ∈ (coreSetupGroup s width band n key).toFinset, f k) =
      ∑ k ∈ (coreIndices s width).toFinset, f k := by
  have hf (key : ℕ × ℕ) : (coreSetupGroup s width band n key).toFinset =
      (coreIndices s width).toFinset.filter (fun k => coreHaloEndpoints s width k band n = key) := by
    ext k
    simp
  simp only [hf]
  exact Finset.sum_fiberwise_of_maps_to
    (fun k hk => Finset.mem_image_of_mem _ hk) f

/-- Every non-full arithmetic group lies in its corresponding movement length
class. This implication does not identify different arithmetic setup keys. -/
theorem coreSetupGroup_in_movement (s width band n k : ℕ) (key : ℕ × ℕ)
    (hne : key ≠ (0,s)) (hk : k ∈ coreSetupGroup s width band n key) :
    k ∈ coreGatherIndices s width (n*band) (key.2-key.1) := by
  obtain ⟨hcore,he⟩ := (mem_coreSetupGroup _ _ _ _ _ _).mp hk
  have hfit := coreHaloEndpoints_fits_of_ne_full s width k band n (by rw [he]; exact hne)
  have hlen : key.2-key.1 = coreLength s width k+2*(n*band) := by
    rw [← he]
    simp only [coreHaloEndpoints,if_pos hfit]
    omega
  simp only [coreGatherIndices,List.mem_filter,decide_eq_true_eq]
  exact ⟨hcore,hfit.1,hfit.2,hlen.symm⟩

end IntegerMultBounds.NLogN.PhaseCellMatrix
