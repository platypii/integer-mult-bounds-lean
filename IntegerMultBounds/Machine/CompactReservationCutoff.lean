import IntegerMultBounds.Machine.CompactReservationGrowth
import IntegerMultBounds.Machine.CompactGlobalRowInitialEndpoint

/-! Honest fallback and nonfallback split for the actual original selected
axes. D≤Q0 uses individual kernels only. D>Q0 admits the proved reservation;
the quantitative cutoff 2Q0 preserves at least half the selected active axes.
This module supplies axis counts and padding costs, not a free implementation
of those individual kernels or of the full recursive layer. -/
namespace IntegerMultBounds.Machine.CompactReservationCutoff
noncomputable section
open Filter Asymptotics Sizes
open CompactReservationGrowth
open CompactGlobalRowPadding

def processed (c m n D : ℕ) := min D (reserved c m n)
def active (c m n D : ℕ) := D-reserved c m n
def cutoff (c m n : ℕ) := 2*reserved c m n

theorem split_axes (c m n D : ℕ) : processed c m n D+active c m n D=D := by
  unfold processed active
  omega

theorem fallback (c m n D : ℕ) (hD : D≤reserved c m n) :
    processed c m n D=D ∧ active c m n D=0 := by
  unfold processed active
  omega

theorem nonfallback (c m n D : ℕ) (hD : reserved c m n<D) :
    processed c m n D=reserved c m n ∧ 0<active c m n D ∧
    CompactGlobalReservation.reservedAxes c m (d n) (guard n) (K n)≤D := by
  unfold processed active reserved at *
  omega

theorem positive_chunk (n : ℕ) : 0<K n := by
  unfold K
  rw [Nat.floor_pos]
  exact Real.one_le_rpow (by exact_mod_cast one_le_d n) spacing_pos.le

theorem positive_reservation (c m n : ℕ) (hc : 2≤c) (hm : 2≤m) : 0<reserved c m n := by
  have hlog : 0<Nat.clog 2 c := Nat.clog_pos (by decide) (by omega)
  have ht : 0<Nat.clog m (2*d n) := Nat.clog_pos (by omega) (by have := one_le_d n; omega)
  have hq := Nat.mul_pos hlog ht
  unfold reserved CompactGlobalReservation.reservedAxes rowAxes
  omega

/-- The cutoff gives a substantial active middle, rather than merely enough
space to fit the reservation. -/
theorem cutoff_ready (c m n D : ℕ) (hc : 2≤c) (hm : 2≤m) (hD : cutoff c m n≤D) :
    reserved c m n<D ∧ D≤2*active c m n D := by
  have hq := positive_reservation c m n hc hm
  unfold cutoff active at *
  omega

theorem eventually_cutoff_small (c m : ℕ) (hm : 2≤m) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, (cutoff c m n:ℝ)≤ε*(d n:ℝ) := by
  filter_upwards [eventually_reservation_small c m hm (ε/2) (by positivity)] with n hn
  unfold cutoff
  push_cast
  linarith

theorem eventually_cutoff_le_dimension (c m : ℕ) (hm : 2≤m) :
    ∀ᶠ n : ℕ in atTop, cutoff c m n≤d n := by
  filter_upwards [eventually_cutoff_small c m hm 1 (by norm_num)] with n hn
  simp only [one_mul] at hn
  exact_mod_cast hn

theorem cutoff_littleO_dimension (c m : ℕ) (hm : 2≤m) :
    (fun n : ℕ => (cutoff c m n:ℝ)) =o[atTop] (fun n => (d n:ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_cutoff_small c m hm ε hε] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hn

/-- Any fixed positive fraction of the actual dimension eventually exceeds
the cutoff. No such statement is made for arbitrary small D. -/
theorem eventually_fraction_ready (c m : ℕ) (hm : 2≤m) (θ : ℝ) (hθ : 0<θ) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, θ*(d n:ℝ)≤(D:ℝ) → cutoff c m n≤D := by
  filter_upwards [eventually_cutoff_small c m hm θ hθ] with n hn D hD
  exact_mod_cast hn.trans hD

/-- Both branches process at most Q0 axes individually. This is a uniform
bound even when the selected D itself depends on n or on a layer. -/
theorem eventually_processed_small (c m : ℕ) (hm : 2≤m) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ, (processed c m n D:ℝ)≤ε*(d n:ℝ) := by
  filter_upwards [eventually_reservation_small c m hm ε hε] with n hn D
  have h : (processed c m n D:ℝ)≤(reserved c m n:ℝ) := by
    exact_mod_cast min_le_right D (reserved c m n)
  exact h.trans hn

/-- Actual original parameters discharge the initial-padding reservation
premise in the nonfallback branch. -/
theorem padding_cost (c m n D P : ℕ) (hc : 2≤c) (hm : 2≤m) (hmc : m≤c)
    (hD : reserved c m n<D) (hDd : D≤d n) (hp : 0<P) :
    CompactGlobalRowInitialRun.cost c m (d n) D (K n) P≤
      (2*(CompactGlobalRowInitialBudget.headerConstant c m+2415))*(2^(D*K n)*P) := by
  have hq : rowAxes c m (d n)≤D := by
    unfold reserved CompactGlobalReservation.reservedAxes at hD
    omega
  exact CompactGlobalRowInitialBudget.original_linear c m (d n) D (K n) P hc hm hmc
    (by have := one_le_d n; omega) (positive_chunk n) hp hDd hq

/-- The physically synthesized row width is the full original compact shape,
including unused fields; it fits solely because this is the nonfallback branch. -/
theorem recordWidth_shape (c m n D P : ℕ) (hD : reserved c m n<D) :
    CompactGlobalRowHeaders.recordWidth c m (d n) D (K n) P=
      (CompactGlobalReservation.shape c m (d n) D (guard n) (K n) P).recordWidth :=
  CompactGlobalRowInitialEndpoint.recordWidth_eq_shape c m (d n) D (guard n) (K n) P
    (positive_chunk n) hD.le

end
end IntegerMultBounds.Machine.CompactReservationCutoff
