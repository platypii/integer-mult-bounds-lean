module

public import IntegerMultBounds.MathlibTM2.Cover.Itinerary

/-! Compute pivot schedules over the residue field by scanning the active column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Itinerary
open Fallback
variable {K : Type*} [Field K] [DecidableEq K] {d : ℕ}

def pivotRow (m : Matrix (Fin d) (Fin d) K) (k : Fin d) : Fin d :=
  ((List.finRange d).find? fun i => decide (k ≤ i ∧ m i k ≠ 0)).getD k

private theorem pivotRow_spec (m : Matrix (Fin d) (Fin d) K) (k : Fin d)
    (existsRow : ∃ i, k ≤ i ∧ IsUnit (m i k)) :
    k ≤ pivotRow m k ∧ IsUnit (m (pivotRow m k) k) := by
  obtain ⟨i,lo,unit⟩ := existsRow
  unfold pivotRow
  cases h : (List.finRange d).find? (fun i => decide (k ≤ i ∧ m i k ≠ 0)) with
  | none =>
    have no := List.find?_eq_none.mp h i (List.mem_finRange i)
    simp [lo,unit.ne_zero] at no
  | some j =>
    have yes : k ≤ j ∧ m j k ≠ 0 := by simpa using List.find?_some h
    exact ⟨yes.1,isUnit_iff_ne_zero.mpr yes.2⟩

/-- The first component records chosen rows, the second the current residue matrix. -/
def pivotStages (m : Matrix (Fin d) (Fin d) K) :
    ℕ → (Fin d → Fin d) × Matrix (Fin d) (Fin d) K
  | 0 => (id,m)
  | n+1 =>
    let (rows,a) := pivotStages m n
    if h : n < d then
      let k : Fin d := ⟨n,h⟩
      let i := pivotRow a k
      let inv := (a i k)⁻¹
      (Function.update rows k i, fun t =>
        if t = k then a i else
          let row := a (Equiv.swap k i t)
          let c := row k * inv
          fun j => row j - c * a i j)
    else (rows,a)

theorem pivotStages_spec (m : Matrix (Fin d) (Fin d) K) (unit : IsUnit m.det) (n : ℕ) (hn : n ≤ d) :
    Valid (pivotStages m n).1 m n ∧ (pivotStages m n).2 = run (pivotStages m n).1 m n := by
  induction n with
  | zero => exact ⟨fun _ _ h => (Nat.not_lt_zero _ h).elim,rfl⟩
  | succ n ih =>
    have h : n < d := hn
    let k : Fin d := ⟨n,h⟩
    let rows := (pivotStages m n).1
    let a := (pivotStages m n).2
    let i := pivotRow a k
    obtain ⟨valid,eq⟩ := ih h.le
    obtain ⟨E,elim,prod,cleared,_⟩ := run_spec rows m n h.le valid
    have det : IsUnit (run rows m n).det := by rw [← prod,Matrix.det_mul]; exact elim.isUnit_det.mul unit
    have chosen : k ≤ i ∧ IsUnit (a i k) := pivotRow_spec a k (by
      change ∃ t, k ≤ t ∧ IsUnit ((pivotStages m n).2 t k)
      rw [eq]; exact exists_unit h cleared det)
    let next := Function.update rows k i
    have agree (j : ℕ) (hj : j ≤ n) : run next m j = run rows m j := run_congr _ _ _ _ fun t ht =>
      Function.update_of_ne (fun e => by have := congrArg Fin.val e; change t.val = n at this; omega) _ _
    simp only [pivotStages,dite_eq_left h]
    constructor
    · apply (valid_succ next m n).mpr
      constructor
      · intro j hj lt
        have ne : (⟨j,hj⟩ : Fin d) ≠ k := fun e => by have := congrArg Fin.val e; change j = n at this; omega
        rw [agree _ lt.le,show next ⟨j,hj⟩ = rows ⟨j,hj⟩ from Function.update_of_ne ne _ _]
        exact valid j hj lt
      · intro _
        rw [agree _ le_rfl,show next k = i from Function.update_self ..]
        exact ⟨chosen.1,eq ▸ chosen.2⟩
    · change _ = run next m (n+1)
      rw [run_succ next m n h]
      change _ = stepOp k (next k) (run next m n) (Ring.inverse (run next m n (next k) k)) * run next m n
      rw [agree _ le_rfl,show next k = i from Function.update_self ..,← show a = run rows m n from eq]
      ext t j
      rw [stepOp_apply]
      by_cases ht : t = k <;> simp [ht,Ring.inverse_eq_inv,k,a,i]

end IntegerMultBounds.MathlibTM2.Cover.Itinerary
