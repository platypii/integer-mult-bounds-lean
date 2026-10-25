module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherLoop

/-! Forward publication of disjoint windows. Each control is the gap before
its window, measured after the preceding window has already been consumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {α : Type*}

def scatterPrefix (L : ℕ) (E X : List α) : List ℕ → List α
  | [] => []
  | d::ds => E.take d ++ X.take L ++ scatterPrefix L (E.drop (d+L)) (X.drop L) ds

def ScatterFits (L : ℕ) (E : List α) : List ℕ → Prop
  | [] => True
  | d::ds => d+L ≤ E.length ∧ ScatterFits L (E.drop (d+L)) ds

def scatterVolume (L : ℕ) (ds : List ℕ) : ℕ := ds.sum+ds.length*L

@[simp] theorem scatterVolume_nil (L : ℕ) : scatterVolume L [] = 0 := by simp [scatterVolume]

@[simp] theorem scatterVolume_cons (L d : ℕ) (ds : List ℕ) :
    scatterVolume L (d::ds) = d+L+scatterVolume L ds := by
  simp only [scatterVolume,List.sum_cons,List.length_cons]; ring

theorem scatterVolume_le (L : ℕ) (E : List α) (ds : List ℕ) (hf : ScatterFits L E ds) :
    scatterVolume L ds ≤ E.length := by
  induction ds generalizing E with
  | nil => simp
  | cons d ds ih =>
    have hh := ih (E.drop (d+L)) hf.2
    simp only [List.length_drop] at hh
    rw [scatterVolume_cons]
    have := hf.1
    omega

theorem length_scatterPrefix (L : ℕ) (E X : List α) (ds : List ℕ)
    (hf : ScatterFits L E ds) (hx : ds.length*L ≤ X.length) :
    (scatterPrefix L E X ds).length = scatterVolume L ds := by
  induction ds generalizing E X with
  | nil => simp [scatterPrefix,scatterVolume]
  | cons d ds ih =>
    have hL : L ≤ X.length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      omega
    have hrest : ds.length*L ≤ (X.drop L).length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      simp only [List.length_drop]; omega
    simp only [scatterPrefix,List.length_append,List.length_take,Nat.min_eq_left (by have := hf.1; omega : d ≤ E.length),
      Nat.min_eq_left hL, ih _ _ hf.2 hrest,scatterVolume_cons]

/-- Finishing the forward sweep leaves the unvisited output suffix in place. -/
def scatterRows (L : ℕ) (E X : List α) (ds : List ℕ) : List α :=
  scatterPrefix L E X ds ++ E.drop (scatterVolume L ds)

theorem length_scatterRows (L : ℕ) (E X : List α) (ds : List ℕ)
    (hf : ScatterFits L E ds) (hx : ds.length*L ≤ X.length) :
    (scatterRows L E X ds).length = E.length := by
  simp only [scatterRows,List.length_append,length_scatterPrefix L E X ds hf hx,List.length_drop]
  have := scatterVolume_le L E ds hf
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
