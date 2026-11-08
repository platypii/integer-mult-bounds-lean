module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountCode
public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloLayout

/-! Identify the arithmetic generator's two-count rows with the monotone
emitter's paired endpoint metadata, including the odd final dummy. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountLayout
open IntegerMultBounds.MathlibTM2.Host HaloIntervalLayout RegularHaloLayout
  RegularHaloCountCode RegularHaloCountRow

theorem pairs_count (L H k N : ℕ) : 2*(pairs L H k N).length = paddedCount N := by
  induction N using Nat.twoStepInduction generalizing k with
  | zero => rfl
  | one => rfl
  | more n ih _ =>
    simp only [pairs,List.length_cons,paddedCount,Nat.mul_add] at *
    have hh := ih (k+2)
    omega

def previousEnd (L H k : ℕ) : ℕ := if k = 0 then 0 else k*L+2*H

theorem metadata_eq_rows {A : ℕ} (V L H k N : ℕ) (hgap : 2*H ≤ L) :
    metadata (A := A) V (previousEnd L H k) (pairs L H k N) =
      ((List.range' k (paddedCount N)).flatMap (values L (2*H) (k+N))).flatMap (binSyms V) := by
  induction N using Nat.twoStepInduction generalizing k with
  | zero => simp [pairs,metadata,paddedCount]
  | one =>
    by_cases hk : k = 0
    · subst k
      simp [pairs,metadata,firstStart,previousEnd,paddedCount,values,List.range'_succ]
    · simp [pairs,metadata,firstStart,previousEnd,hk,paddedCount,values,List.range'_succ,
        Nat.add_mul,List.append_assoc]
      congr 1
      omega
  | more n ih _ =>
    have hfirst : (k+1)*L-previousEnd L H k = if k = 0 then L else L-2*H := by
      by_cases hk : k = 0
      · simp [previousEnd,hk]
      · simp only [previousEnd,ite_eq_right hk,Nat.add_mul,Nat.one_mul]
        omega
    have hnext := pairs_firstStart L H (k+2) n ((k+2)*L+2*H)
    have hprev : previousEnd L H (k+2) = (k+2)*L+2*H := by simp [previousEnd]
    have hp : paddedCount (n+2) = paddedCount n+2 := by unfold paddedCount; omega
    simp only [pairs,metadata]
    rw [hnext,hfirst]
    have ht := ih (k+2)
    rw [hprev] at ht
    have hadd : k+2+n = k+(n+2) := by omega
    rw [hadd] at ht
    rw [ht]
    have hkeep : (k+1)*L+2*H-(k+1)*L = 2*H := by omega
    have hlast : (k+2)*L+2*H-((k+1)*L+2*H) = L := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    have hbody : (k+2)*L-((k+1)*L+2*H) = L-2*H := by
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    have hkeep₂ : (k+2)*L+2*H-(k+2)*L = 2*H := by omega
    rw [hkeep]
    rw [hp]
    by_cases hn : n = 0
    · subst n
      simp [values,paddedCount,List.range'_succ,List.append_assoc,Nat.add_assoc,hlast]
    · have hpos : 0 < n := by omega
      simp [values,hn,hpos,List.range'_succ,List.append_assoc,hbody,hkeep₂,
        Nat.add_assoc]

theorem metadata_eq_countValues {A : ℕ} (V L H N : ℕ) (hgap : 2*H ≤ L) :
    metadata (A := A) V 0 (pairs L H 0 N) = (countValues L (2*H) N).flatMap (binSyms V) := by
  simpa [previousEnd,countValues,List.range_eq_range'] using metadata_eq_rows (A := A) V L H 0 N hgap

end IntegerMultBounds.MathlibTM2.Routing.RegularHaloCountLayout
