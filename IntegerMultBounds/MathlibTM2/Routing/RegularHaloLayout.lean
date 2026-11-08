module

public import IntegerMultBounds.MathlibTM2.Routing.HaloIntervalLayout

/-! The manuscript's persistent target halos [kL-A,(k+1)L+A), expressed in
an A-extended row. An odd final window is paired with an empty interval. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloLayout
open HaloIntervalLayout
variable {β : Type}

/-- Coordinates are shifted by the prepended halo, so starts are k*L. -/
def pairs (L H k : ℕ) : ℕ → List IntervalPair
  | 0 => []
  | 1 => [⟨k*L,(k+1)*L+2*H,(k+1)*L+2*H,(k+1)*L+2*H⟩]
  | n+2 => ⟨k*L,(k+1)*L+2*H,(k+1)*L,(k+2)*L+2*H⟩::pairs L H (k+2) n

theorem pairs_firstStart (L H k n fallback : ℕ) :
    firstStart fallback (pairs L H k n) = if n = 0 then fallback else k*L := by
  cases n with
  | zero => rfl
  | succ n => cases n <;> rfl

theorem pairs_lastEnd (L H k n prev : ℕ) :
    lastEnd prev (pairs L H k n) = if n = 0 then prev else (k+n)*L+2*H := by
  induction n using Nat.twoStepInduction generalizing k prev with
  | zero => rfl
  | one => simp [pairs,lastEnd]
  | more n ih _ =>
    simp only [pairs,lastEnd,ih]
    by_cases hn : n = 0
    · subst n; simp
    · simp [hn,Nat.add_left_comm,Nat.add_comm]

theorem pairs_valid (L H : ℕ) (hgap : 2*H ≤ L) (k n prev : ℕ)
    (hlo : k*L ≤ prev) (hhi : prev ≤ (k+1)*L) : Valid prev (pairs L H k n) := by
  induction n using Nat.twoStepInduction generalizing k prev with
  | zero => trivial
  | one =>
    simp only [pairs,Valid,firstStart]
    exact ⟨hlo,by omega,le_rfl,le_rfl,le_rfl,trivial⟩
  | more n ih _ =>
    have hn := pairs_firstStart L H (k+2) n ((k+2)*L+2*H)
    have hnext : (k+2)*L ≤ firstStart ((k+2)*L+2*H) (pairs L H (k+2) n) ∧
        firstStart ((k+2)*L+2*H) (pairs L H (k+2) n) ≤ (k+2)*L+2*H := by
      rw [hn]
      split <;> omega
    change k*L ≤ prev ∧ prev ≤ (k+1)*L ∧ (k+1)*L ≤ (k+1)*L+2*H ∧
      (k+1)*L+2*H ≤ firstStart ((k+2)*L+2*H) (pairs L H (k+2) n) ∧
      firstStart ((k+2)*L+2*H) (pairs L H (k+2) n) ≤ (k+2)*L+2*H ∧
      Valid ((k+2)*L+2*H) (pairs L H (k+2) n)
    refine ⟨hlo,hhi,by omega,?_,hnext.2,ih (k+2) ((k+2)*L+2*H) (by omega) ?_⟩
    · simp only [Nat.add_mul,Nat.one_mul] at hnext ⊢
      omega
    · simp only [Nat.add_mul,Nat.one_mul]
      omega

theorem pairs_length_le (L H k n : ℕ) : (pairs L H k n).length ≤ n := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [pairs]
  | one => simp [pairs]
  | more n ih _ =>
    simp only [pairs,List.length_cons]
    have hh := ih (k+2)
    omega

theorem pairs_windows (row : List β) (L H k n : ℕ) :
    windows row (pairs L H k n) =
      (List.range' k n).flatMap (fun j => slice row (j*L) ((j+1)*L+2*H)) := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => rfl
  | one => simp [pairs,windows,slice]
  | more n ih _ =>
    change (slice row (k*L) ((k+1)*L+2*H)++slice row ((k+1)*L) ((k+2)*L+2*H))++
      windows row (pairs L H (k+2) n) = _
    rw [ih]
    simp [List.range'_succ,List.append_assoc,Nat.add_assoc]

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloLayout
