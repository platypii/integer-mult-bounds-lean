import IntegerMultBounds.Machine.CompactReservedVolumeBudget

/-! The complete fixed nonfallback programs have the actual certified saving.
These budgets include generated headers and all controls, not only abstract
per-axis costs. Exact physical runtime bounds are used as the witnesses. -/
namespace IntegerMultBounds.Machine.CompactReservedActualBudget
noncomputable section
open Filter Sizes Parameters
open CompactReservationGrowth (guard reserved)
open CompactFallbackScalars (precision)
open CompactFallbackActualBudget (baseVolume volume_le_base)
open CompactFallbackAxisRun (Array Width word)
open CompactFallbackSemantics (decoded)
open Networks

def cost (c m n D rho : ℕ) := CompactReservedOriginal.cost c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
def roundtripCost (c m n D rho : ℕ) := CompactReservedRoundtrip.cost c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
def constant (c m : ℕ) := 5*CompactReservedVolumeBudget.constant c m
def roundtripConstant (c m : ℕ) := 5*(2*CompactReservedVolumeBudget.constant c m+1)

theorem cost_le (c m n D rho : ℕ) (hc : 2≤c) (hD : D≤d n) (hres : reserved c m n≤D) :
    cost c m n D rho≤constant c m*baseVolume n D*reserved c m n := by
  have hh := CompactReservedVolumeBudget.cost_linear c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
    hc (one_le_d n) (by unfold CompactReservationGrowth.guard; omega) (CompactReservationCutoff.positive_chunk n) hres
  have hv := Nat.mul_le_mul_right (reserved c m n)
    (Nat.mul_le_mul_left (CompactReservedVolumeBudget.constant c m) (volume_le_base n D hD))
  simpa only [cost,constant,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh.trans hv

theorem roundtripCost_le (c m n D rho : ℕ) (hc : 2≤c) (hD : D≤d n) (hres : reserved c m n≤D) :
    roundtripCost c m n D rho≤roundtripConstant c m*baseVolume n D*reserved c m n := by
  have hh := CompactReservedVolumeBudget.roundtrip_cost_linear c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
    hc (one_le_d n) (by unfold CompactReservationGrowth.guard; omega) (CompactReservationCutoff.positive_chunk n) hres
  have hv := Nat.mul_le_mul_right (reserved c m n)
    (Nat.mul_le_mul_left (2*CompactReservedVolumeBudget.constant c m+1) (volume_le_base n D hD))
  simpa only [roundtripCost,roundtripConstant,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh.trans hv

private theorem eventually_scale (c m C : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ V : ℕ,
      (C*V*reserved c m n:ℝ)≤η*(V:ℝ)*(d n:ℝ)^lam' := by
  have hs : (0:ℝ)<C+1 := by positivity
  filter_upwards [CompactReservationRate.eventually_reserved_power c m hm lam' (η/(C+1))
    CompactReservationRate.certified_exponent (div_pos hη hs)] with n hn V
  have he := (le_div_iff₀ hs).mp (show (reserved c m n:ℝ)≤(η*(d n:ℝ)^lam')/(C+1) by
    convert hn using 1; ring)
  have hscale := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) V)
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) (d n)) lam']

theorem eventually_cost (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → reserved c m n≤D →
      (cost c m n D rho:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_scale c m (constant c m) hm η hη] with n hn D rho hD hres
  have hh : (cost c m n D rho:ℝ)≤(constant c m:ℝ)*(baseVolume n D:ℝ)*(reserved c m n:ℝ) := by
    exact_mod_cast cost_le c m n D rho hc hD hres
  exact hh.trans (hn _)

theorem eventually_roundtripCost (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → reserved c m n≤D →
      (roundtripCost c m n D rho:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_scale c m (roundtripConstant c m) hm η hη] with n hn D rho hD hres
  have hh : (roundtripCost c m n D rho:ℝ)≤(roundtripConstant c m:ℝ)*(baseVolume n D:ℝ)*(reserved c m n:ℝ) := by
    exact_mod_cast roundtripCost_le c m n D rho hc hD hres
  exact hh.trans (hn _)

/-- A concrete fixed one-pass machine and its actual fully paid cost witness. -/
theorem eventually_execution (inverse : Bool) (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → reserved c m n≤D → rho<K n →
      ∀ f : Array D (K n) (ℓ n), Width D (K n) (ℓ n) (precision n) f →
      ∃ t : ℕ, HoareTime (CompactReservedOriginal.program inverse c m)
        (fun v => v=CompactReservedSchedule.bank (CompactReservedHeaders.initial D (K n) rho (ℓ n) (precision n) (d n) (guard n)) (word f))
        (fun v => v=CompactReservedSchedule.bank (CompactReservedHeaders.initial D (K n) rho (ℓ n) (precision n) (d n) (guard n))
          (word (CompactReservedOriginal.result inverse c m D (K n) rho (ℓ n) (precision n) (d n) (guard n) f))) t ∧
        (t:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_cost c m hc hm η hη] with n hn D rho hD hres hr f hw
  exact ⟨cost c m n D rho,CompactReservedOriginal.runs inverse c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
    hc hm (one_le_d n) (CompactReservationCutoff.positive_chunk n) hr hres f hw,hn D rho hD hres⟩

/-- The actual fully paid roundtrip both recovers every polynomial coordinate
and satisfies the certified saving, with no inverse normalization assumption. -/
theorem eventually_roundtrip (c m : ℕ) (hc : 2≤c) (hm : 2≤m) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n : ℕ in atTop, ∀ D rho : ℕ, D≤d n → reserved c m n≤D → rho<K n →
      ∀ f : Array D (K n) (ℓ n), Width D (K n) (ℓ n) (precision n) f →
      (∀ i,‖decoded D (K n) (ℓ n) (precision n) 0 f i‖≤1) →
      ∃ t : ℕ, HoareTime (CompactReservedRoundtrip.program c m)
        (fun v => v=CompactReservedSchedule.bank (CompactReservedHeaders.initial D (K n) rho (ℓ n) (precision n) (d n) (guard n)) (word f))
        (fun v => v=CompactReservedSchedule.bank (CompactReservedHeaders.initial D (K n) rho (ℓ n) (precision n) (d n) (guard n))
          (word (CompactReservedRoundtrip.result c m D (K n) rho (ℓ n) (precision n) (d n) (guard n) f)) ∧
          ∀ r : Fin (CompactFallbackHeaders.polynomials (ℓ n)),
            (fun x => decoded D (K n) (ℓ n) (precision n) (2*reserved c m n)
              (CompactReservedRoundtrip.result c m D (K n) rho (ℓ n) (precision n) (d n) (guard n) f)
              (FlatCoordinateLayout.index x r))=
            (fun x => decoded D (K n) (ℓ n) (precision n) 0 f (FlatCoordinateLayout.index x r))) t ∧
        (t:ℝ)≤η*(baseVolume n D:ℝ)*(d n:ℝ)^lam' := by
  filter_upwards [eventually_roundtripCost c m hc hm η hη] with n hn D rho hD hres hr f hw hu
  exact ⟨roundtripCost c m n D rho,CompactReservedRoundtrip.correct c m D (K n) rho (ℓ n) (precision n) (d n) (guard n)
    hc hm (one_le_d n) (CompactReservationCutoff.positive_chunk n) hr hres f hw hu,hn D rho hD hres⟩

end
end IntegerMultBounds.Machine.CompactReservedActualBudget
