module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterData

/-! Observable publication semantics: every selected window is the matching
solution row, while its preceding gap and the unvisited suffix are preserved. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {α : Type*}

@[simp] theorem scatterRows_nil (L : ℕ) (E X : List α) : scatterRows L E X [] = E := by
  simp [scatterRows,scatterPrefix]

theorem scatterRows_cons (L d : ℕ) (ds : List ℕ) (E X : List α) :
    scatterRows L E X (d::ds) = E.take d ++ X.take L ++
      scatterRows L (E.drop (d+L)) (X.drop L) ds := by
  simp only [scatterRows,scatterPrefix,scatterVolume_cons,List.drop_drop,List.append_assoc]

theorem scatterRows_gap (L d : ℕ) (ds : List ℕ) (E X : List α) (hd : d ≤ E.length) :
    (scatterRows L E X (d::ds)).take d = E.take d := by
  rw [scatterRows_cons,List.append_assoc]
  exact List.take_left' (by simp [List.length_take,Nat.min_eq_left hd])

theorem scatterRows_head (L d : ℕ) (ds : List ℕ) (E X : List α)
    (hd : d ≤ E.length) (hx : L ≤ X.length) :
    ((scatterRows L E X (d::ds)).drop d).take L = X.take L := by
  rw [scatterRows_cons,List.append_assoc,List.drop_left' (by simp [List.length_take,Nat.min_eq_left hd])]
  exact List.take_left' (by simp [List.length_take,Nat.min_eq_left hx])

theorem scatterRows_tail (L d : ℕ) (ds : List ℕ) (E X : List α)
    (hd : d ≤ E.length) (hx : L ≤ X.length) :
    (scatterRows L E X (d::ds)).drop (d+L) = scatterRows L (E.drop (d+L)) (X.drop L) ds := by
  rw [scatterRows_cons]
  exact List.drop_left' (by simp [List.length_append,List.length_take,Nat.min_eq_left hd,Nat.min_eq_left hx])

def scatterWindowOffset (L : ℕ) (ds : List ℕ) (n : ℕ) : ℕ :=
  (ds.take (n+1)).sum+n*L

@[simp] theorem scatterWindowOffset_zero (L d : ℕ) (ds : List ℕ) :
    scatterWindowOffset L (d::ds) 0 = d := by simp [scatterWindowOffset]

@[simp] theorem scatterWindowOffset_succ (L d n : ℕ) (ds : List ℕ) :
    scatterWindowOffset L (d::ds) (n+1) = d+L+scatterWindowOffset L ds n := by
  simp [scatterWindowOffset,List.take_succ_cons,List.sum_cons]; ring

/-- The published word slice agrees exactly with its row in the packed solver output. -/
theorem scatterRows_window (L : ℕ) (ds : List ℕ) (E X : List α)
    (hf : ScatterFits L E ds) (hx : ds.length*L ≤ X.length)
    (n : ℕ) (hn : n < ds.length) :
    ((scatterRows L E X ds).drop (scatterWindowOffset L ds n)).take L = (X.drop (n*L)).take L := by
  induction ds generalizing E X n with
  | nil => simp at hn
  | cons d ds ih =>
    have hd : d ≤ E.length := by have := hf.1; omega
    have hL : L ≤ X.length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      omega
    cases n with
    | zero => simpa only [scatterWindowOffset_zero,Nat.zero_mul,List.drop_zero] using scatterRows_head L d ds E X hd hL
    | succ n =>
      have hrest : ds.length*L ≤ (X.drop L).length := by
        simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
        simp only [List.length_drop]; omega
      rw [scatterWindowOffset_succ,← List.drop_drop,scatterRows_tail L d ds E X hd hL,
        ih _ _ hf.2 hrest n (by simpa using hn),List.drop_drop]
      congr 2
      ring

/-- Publication preserves every symbol outside the selected windows. -/
theorem scatterRows_off (L : ℕ) (ds : List ℕ) (E X : List α)
    (hf : ScatterFits L E ds) (hx : ds.length*L ≤ X.length) (j : ℕ)
    (hoff : ∀ n, n < ds.length → j < scatterWindowOffset L ds n ∨
      scatterWindowOffset L ds n+L ≤ j) :
    (scatterRows L E X ds)[j]? = E[j]? := by
  induction ds generalizing E X j with
  | nil => simp
  | cons d ds ih =>
    have hd : d ≤ E.length := by have := hf.1; omega
    have hL : L ≤ X.length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      omega
    by_cases hj : j < d
    · rw [scatterRows_cons,List.append_assoc,List.getElem?_append_left
        (by simp [List.length_take,Nat.min_eq_left hd]; exact hj),List.getElem?_take_of_lt hj]
    have hafter : d+L ≤ j := by
      have hh := hoff 0 (by simp)
      simpa only [scatterWindowOffset_zero,or_iff_right hj] using hh
    have hrest : ds.length*L ≤ (X.drop L).length := by
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul] at hx
      simp only [List.length_drop]; omega
    have he := ih (E.drop (d+L)) (X.drop L) hf.2 hrest (j-(d+L)) (by
      intro n hn
      have hh := hoff (n+1) (by simpa using hn)
      rw [scatterWindowOffset_succ] at hh
      omega)
    rw [← scatterRows_tail L d ds E X hd hL,List.getElem?_drop,List.getElem?_drop] at he
    simpa only [Nat.add_sub_of_le hafter] using he

/-- A borrowed output suffix lies beyond the owned ambient line and is untouched. -/
theorem scatterRows_append (L : ℕ) (ds : List ℕ) (E X tail : List α)
    (hf : ScatterFits L E ds) :
    scatterRows L (E++tail) X ds = scatterRows L E X ds ++ tail := by
  induction ds generalizing E X with
  | nil => simp
  | cons d ds ih =>
    have hd : d ≤ E.length := by have := hf.1; omega
    rw [scatterRows_cons,scatterRows_cons,List.take_append_of_le_length hd,
      List.drop_append_of_le_length hf.1,ih _ _ hf.2]
    simp only [List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
