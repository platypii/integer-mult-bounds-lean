module

public import IntegerMultBounds.MathlibTM2.Routing.ManuscriptHaloAxes
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! Exact dyadic target-grid geometry for the executed retained-halo pass.
This does not identify the prime source grid with the dyadic target grid. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost.SelectedHaloGeometry
open IntegerMultBounds.MathlibTM2.Mult
open IntegerMultBounds.MathlibTM2.Routing
open HaloManuscriptSizing RetainedHaloTensor
open scoped BigOperators

def exponent (n : ℕ) (i : Fin (Sizes.d n)) : ℕ :=
  if i.val < Sizes.numHalf n then Sizes.ℓ n-1 else Sizes.ℓ n

def axis (n : ℕ) (i : Fin (Sizes.d n)) : Axis where
  N := 2^(exponent n i-Nat.clog 2 (Sizes.p n^8))
  L := core (Sizes.p n)
  H := halo (Sizes.p n)
  N_pos := Nat.two_pow_pos _
  L_pos := Nat.two_pow_pos _

theorem coreExponent_le (p : ℕ) : Nat.clog 2 (p^8) ≤ 8*Nat.clog 2 p := by
  apply Nat.clog_le_of_le_pow
  calc
    p^8 ≤ (2^Nat.clog 2 p)^8 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) 8
    _ = 2^(8*Nat.clog 2 p) := by rw [←pow_mul]; congr 1; omega

theorem room {n : ℕ} (h : Sizes.Big n)
    (hk : 16*Nat.clog 2 (Sizes.p n) ≤ Sizes.K n) :
    2*Nat.clog 2 (Sizes.p n^8) ≤ Sizes.ℓ n-1 := by
  have hh := coreExponent_le (Sizes.p n)
  have hl := h.K_succ_le_ℓ
  omega

theorem eventually_room : ∀ᶠ n in Filter.atTop,
    2*Nat.clog 2 (Sizes.p n^8) ≤ Sizes.ℓ n-1 := by
  filter_upwards [Sizes.eventually_big, Sizes.eventually_clog_p_le_K 16] with n hn hk
  exact room hn hk

theorem length_eq {n : ℕ}
    (hroom : 2*Nat.clog 2 (Sizes.p n^8) ≤ Sizes.ℓ n-1) (i : Fin (Sizes.d n)) :
    (axis n i).N*(axis n i).L = Sizes.t n i := by
  have he : Nat.clog 2 (Sizes.p n^8) ≤ exponent n i := by
    unfold exponent
    split_ifs <;> omega
  change 2^(exponent n i-Nat.clog 2 (Sizes.p n^8))*2^Nat.clog 2 (Sizes.p n^8) = _
  rw [←pow_add,Nat.sub_add_cancel he]
  unfold exponent Sizes.t
  split_ifs <;> rfl

theorem coarse_room {n : ℕ}
    (hroom : 2*Nat.clog 2 (Sizes.p n^8) ≤ Sizes.ℓ n-1) (i : Fin (Sizes.d n)) :
    (axis n i).L ≤ (axis n i).N := by
  change 2^Nat.clog 2 (Sizes.p n^8) ≤ 2^(exponent n i-Nat.clog 2 (Sizes.p n^8))
  apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
  unfold exponent
  split_ifs <;> omega

theorem volume_eq {n : ℕ} (h : Sizes.Big n)
    (hroom : 2*Nat.clog 2 (Sizes.p n^8) ≤ Sizes.ℓ n-1) :
    volume (axis n) ∅ = Sizes.T n := by
  calc
    _ = ∏ i, Sizes.t n i := by
      apply Finset.prod_congr rfl
      intro i _
      simpa only [localLength,Finset.notMem_empty,ite_false] using length_eq hroom i
    _ = _ := Sizes.prod_t h.one_le_d

/-- Selected precision leaves room for all global archive metadata. -/
theorem bytes_le {n : ℕ} (h : Sizes.Big n) (hp : 4 ≤ Sizes.p n) (w : ℕ)
    (hw : w ≤ Sizes.p n^2) :
    Sizes.T n*w ≤ 2^(Sizes.p n^2-4) := by
  have hlog : Sizes.logT n ≤ Sizes.p n := by
    have hh := h.logT_bounds.2
    unfold Sizes.p
    omega
  have hw' : w ≤ 2^(2*Sizes.p n) := by
    calc
      w ≤ Sizes.p n^2 := hw
      _ ≤ (2^Sizes.p n)^2 :=
        Nat.pow_le_pow_left (HaloSetupResource.self_le_two_pow _) 2
      _ = _ := by rw [←pow_mul]; congr 1; omega
  have hpoly : 3*Sizes.p n+4 ≤ Sizes.p n^2 := by nlinarith
  have hroom : Sizes.logT n+2*Sizes.p n ≤ Sizes.p n^2-4 := by omega
  calc
    _ ≤ Sizes.T n*2^(2*Sizes.p n) := Nat.mul_le_mul_left _ hw'
    _ = 2^(Sizes.logT n+2*Sizes.p n) := by rw [Sizes.T,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hroom

theorem dimension_le {n : ℕ} (h : Sizes.Big n) : Sizes.d n ≤ Sizes.p n := by
  have hh := h.ℓ_bounds.2
  have hl := h.four_le_ℓ
  nlinarith

end IntegerMultBounds.MathlibTM2.Cost.SelectedHaloGeometry
