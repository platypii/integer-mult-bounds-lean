module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowError

/-! Coupling errors separate computed-input error, controlled by row mass,
from coefficient error and arithmetic truncation, controlled by actual support. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem coupling_row_perturb {ι : Type*} (entries : List ι) (a c x y : ι → ℝ)
    (Y δ ε K : ℝ) (hY : 0 ≤ Y) (hε : 0 ≤ ε)
    (hx : ∀ j ∈ entries, |x j| ≤ Y) (hc : ∀ j ∈ entries, |c j-a j| ≤ δ)
    (hy : ∀ j ∈ entries, |x j-y j| ≤ ε)
    (hmass : (entries.map (fun j => |a j|)).sum ≤ K) :
    |(entries.map (fun j => x j*c j)).sum-(entries.map (fun j => y j*a j)).sum| ≤
      entries.length*(Y*δ)+K*ε := by
  have hterm (j : ι) (hj : j ∈ entries) :
      |x j*c j-y j*a j| ≤ Y*δ+|a j| *ε := by
    calc
      _ = |x j*(c j-a j)+a j*(x j-y j)| := by congr 1; ring
      _ ≤ |x j*(c j-a j)|+|a j*(x j-y j)| := abs_add_le _ _
      _ = |x j| *|c j-a j|+|a j| *|x j-y j| := by rw [abs_mul,abs_mul]
      _ ≤ Y*δ+|a j| *ε := add_le_add
        (mul_le_mul (hx j hj) (hc j hj) (abs_nonneg _) hY)
        (mul_le_mul_of_nonneg_left (hy j hj) (abs_nonneg _))
  have hsum : |(entries.map (fun j => x j*c j)).sum-(entries.map (fun j => y j*a j)).sum| ≤
      entries.length*(Y*δ)+(entries.map (fun j => |a j|)).sum*ε := by
    induction entries with
    | nil => simp
    | cons j entries ih =>
      have hh := hterm j (by simp)
      have ht := ih (fun j hj => hx j (by simp [hj])) (fun j hj => hc j (by simp [hj]))
        (fun j hj => hy j (by simp [hj]))
        (by simp only [List.map_cons,List.sum_cons] at hmass
            linarith [abs_nonneg (a j)])
        (fun j hj => hterm j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons]
      calc
        _ = |(x j*c j-y j*a j)+((entries.map (fun j => x j*c j)).sum-
            (entries.map (fun j => y j*a j)).sum)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
        _ ≤ (Y*δ+|a j| *ε)+(entries.length*(Y*δ)+(entries.map (fun j => |a j|)).sum*ε) :=
          add_le_add hh ht
        _ = (j::entries).length*(Y*δ)+(|a j|+(entries.map (fun j => |a j|)).sum)*ε := by
          simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring
  exact hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hmass hε))

theorem coupling_residual_perturb {ι : Type*} (entries : List ι) (a c x y : ι → ℝ)
    (rhs b out Y δ ε K arithmetic rhsError : ℝ)
    (hY : 0 ≤ Y) (hε : 0 ≤ ε)
    (hx : ∀ j ∈ entries, |x j| ≤ Y) (hc : ∀ j ∈ entries, |c j-a j| ≤ δ)
    (hy : ∀ j ∈ entries, |x j-y j| ≤ ε)
    (hmass : (entries.map (fun j => |a j|)).sum ≤ K)
    (hrow : |out-(rhs-(entries.map (fun j => x j*c j)).sum)| ≤ arithmetic)
    (hrhs : |rhs-b| ≤ rhsError) :
    |out-(b-(entries.map (fun j => y j*a j)).sum)| ≤
      arithmetic+rhsError+entries.length*(Y*δ)+K*ε := by
  have hh := coupling_row_perturb entries a c x y Y δ ε K hY hε hx hc hy hmass
  calc
    _ = |(out-(rhs-(entries.map (fun j => x j*c j)).sum))+
        ((rhs-b)-((entries.map (fun j => x j*c j)).sum-(entries.map (fun j => y j*a j)).sum))| := by
      congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ arithmetic+(rhsError+(entries.length*(Y*δ)+K*ε)) :=
      add_le_add hrow ((abs_sub _ _).trans (add_le_add hrhs hh))
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
