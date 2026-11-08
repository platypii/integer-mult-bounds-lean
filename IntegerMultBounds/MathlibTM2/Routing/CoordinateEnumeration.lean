module

public import IntegerMultBounds.MathlibTM2.Routing.HaloRecordLayout
import Mathlib.Data.List.Nodup

/-! Structural lexicographic enumeration in a specified field order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.CoordinateEnumeration
variable {ι : Type} [DecidableEq ι]

def enumerate (width : ι → ℕ) : List ι → (ι → ℕ) → List (ι → ℕ)
  | [], base => [base]
  | i :: fields, base => (List.range (width i)).flatMap fun t =>
      enumerate width fields (Function.update base i t)

theorem enumerate_length (width : ι → ℕ) (fields : List ι) (base : ι → ℕ) :
    (enumerate width fields base).length = (fields.map width).prod := by
  induction fields generalizing base with
  | nil => simp [enumerate]
  | cons i fields ih =>
    simp only [enumerate]
    rw [HaloRecordLayout.length_flatMap _ _ _ (by intro t _; exact ih _)]
    simp

theorem mem_enumerate (width : ι → ℕ) (fields : List ι) (hn : fields.Nodup) (base coords : ι → ℕ) :
    coords ∈ enumerate width fields base ↔
      (∀ i ∈ fields, coords i < width i) ∧ (∀ i, i ∉ fields → coords i = base i) := by
  induction fields generalizing base with
  | nil =>
    simp only [enumerate,List.mem_singleton,List.not_mem_nil]
    constructor
    · intro he; exact ⟨by simp,fun _ _ => congrFun he _⟩
    · intro h; exact funext (fun i => h.2 i (by simp))
  | cons i fields ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    simp only [enumerate,List.mem_flatMap,List.mem_range]
    constructor
    · rintro ⟨t,ht',hc⟩
      obtain ⟨hv,hrest⟩ := (ih ht _).mp hc
      have he : coords i = t := by simpa using hrest i hi
      refine ⟨?_,?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · simpa only [he] using ht'
        · exact hv j hj
      · intro j hj
        have hji : j ≠ i := fun he => hj (by simp [he])
        have hjt : j ∉ fields := fun he => hj (List.mem_cons_of_mem i he)
        simpa only [Function.update_of_ne hji] using hrest j hjt
    · rintro ⟨hv,hrest⟩
      refine ⟨coords i,hv i (by simp),(ih ht _).mpr ⟨?_,?_⟩⟩
      · intro j hj; exact hv j (List.mem_cons_of_mem i hj)
      · intro j hj
        by_cases hji : j = i
        · subst j; simp
        · rw [Function.update_of_ne hji]
          exact hrest j (by simp [hji,hj])

theorem enumerate_append (width : ι → ℕ) (xs ys : List ι) (base : ι → ℕ) :
    enumerate width (xs++ys) base = (enumerate width xs base).flatMap (enumerate width ys) := by
  induction xs generalizing base with
  | nil => simp [enumerate]
  | cons i xs ih => simp only [List.cons_append,enumerate,ih,List.flatMap_assoc]

theorem enumerate_nodup (width : ι → ℕ) (fields : List ι) (hn : fields.Nodup) (base : ι → ℕ) :
    (enumerate width fields base).Nodup := by
  induction fields generalizing base with
  | nil => simp [enumerate]
  | cons i fields ih =>
    have hi := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    apply List.nodup_flatMap.mpr
    refine ⟨fun t _ => ih ht _,?_⟩
    apply (show (List.range (width i)).Nodup from List.nodup_range).imp
    intro t u htu
    apply List.disjoint_left.mpr
    intro coords hc hd
    have hc' := ((mem_enumerate width fields ht _ coords).mp hc).2 i hi
    have hd' := ((mem_enumerate width fields ht _ coords).mp hd).2 i hi
    simp only [Function.update_self] at hc' hd'
    exact htu (hc'.symm.trans hd')

end IntegerMultBounds.MathlibTM2.Routing.CoordinateEnumeration
