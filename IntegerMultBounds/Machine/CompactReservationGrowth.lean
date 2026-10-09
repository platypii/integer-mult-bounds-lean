import IntegerMultBounds.Machine.CompactGuardGrowth
import IntegerMultBounds.Machine.CompactGlobalReservation

/-! The manuscript's actual original-axis reservation is sublinear in the
actual dimension. This never asserts that a small selected-axis set contains
the full reservation; the fallback decision is formalized separately. -/
namespace IntegerMultBounds.Machine.CompactReservationGrowth
noncomputable section
open Filter Asymptotics Sizes CompactScalarAllowances
open CompactGadgetReservationCapacity CompactGlobalRowPadding

def guard (n : ℕ) := 4*guardLog n+6
def reserved (c m n : ℕ) := CompactGlobalReservation.reservedAxes c m (d n) (guard n) (K n)

theorem rowAxes_le_guardLog (c m n : ℕ) (hm : 2≤m) :
    rowAxes c m (d n)≤Nat.clog 2 c*guardLog n := by
  have hdim : 2*d n≤6*b n := by nlinarith [d_le_b n]
  have hlog : Nat.clog m (2*d n)≤guardLog n :=
    Nat.clog_mono (by decide : 1<2) hm hdim
  exact Nat.mul_le_mul_left _ hlog

theorem fields_bound (d G K : ℕ) (hK : 0<K) :
    ((frontChunks d G K+backChunks d G K:ℕ):ℝ)*(K:ℝ)≤3*(d:ℝ)*(G:ℝ)+2*(K:ℝ) := by
  have hf := (Compact.Layout.ceiling_chunks (2*capacity d G) K hK).2
  have hb := (Compact.Layout.ceiling_chunks (capacity d G) K hK).2
  change frontChunks d G K*K<2*(d*G)+K at hf
  change backChunks d G K*K<d*G+K at hb
  have h : (frontChunks d G K+backChunks d G K)*K≤3*d*G+2*K := by nlinarith
  exact_mod_cast h

/-- A quantitative bound from the actual guard/chunk ratio. -/
theorem reservation_bound (c m n : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η)
    (hs : (guardLog n:ℝ)+1≤η*(K n:ℝ)) :
    (reserved c m n:ℝ)≤((Nat.clog 2 c:ℝ)+20)*η*(d n:ℝ) := by
  have hK : 0<K n := by
    by_contra hh
    have hz : K n=0 := by omega
    rw [hz,Nat.cast_zero,mul_zero] at hs
    have hn : (0:ℝ)≤guardLog n := Nat.cast_nonneg _
    linarith
  have hKr : (0:ℝ)<K n := by exact_mod_cast hK
  have hk : (K n:ℝ)≤d n := by exact_mod_cast chunk_le_dimension n
  have hsmall : (guardLog n:ℝ)+1≤η*(d n:ℝ) :=
    hs.trans (mul_le_mul_of_nonneg_left hk hη.le)
  have hrow : (rowAxes c m (d n):ℝ)≤(Nat.clog 2 c:ℝ)*(guardLog n:ℝ) := by
    exact_mod_cast rowAxes_le_guardLog c m n hm
  have hrow' : (rowAxes c m (d n):ℝ)≤(Nat.clog 2 c:ℝ)*(η*(d n:ℝ)) := by
    exact hrow.trans (mul_le_mul_of_nonneg_left (by linarith : (guardLog n:ℝ)≤η*(d n:ℝ)) (Nat.cast_nonneg _))
  have hguard : (guard n:ℝ)≤6*η*(K n:ℝ) := by
    unfold guard
    push_cast
    nlinarith only [hs,Nat.cast_nonneg (α := ℝ) (guardLog n)]
  have hfields := fields_bound (d n) (guard n) (K n) hK
  have hmul := mul_le_mul_of_nonneg_left hguard (show (0:ℝ)≤3*(d n:ℝ) by positivity)
  have hfields' : ((frontChunks (d n) (guard n) (K n)+backChunks (d n) (guard n) (K n):ℕ):ℝ)≤
      18*η*(d n:ℝ)+2 := by
    apply (mul_le_mul_iff_left₀ hKr).mp
    nlinarith only [hfields,hmul]
  have htwo : (2:ℝ)≤2*η*(d n:ℝ) := by
    nlinarith only [hsmall,Nat.cast_nonneg (α := ℝ) (guardLog n)]
  unfold reserved CompactGlobalReservation.reservedAxes
  push_cast at hfields' ⊢
  nlinarith only [hrow',hfields',htwo]

theorem eventually_reservation_small (c m : ℕ) (hm : 2≤m) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, (reserved c m n:ℝ)≤ε*(d n:ℝ) := by
  have hden : (0:ℝ)<(Nat.clog 2 c:ℝ)+20 := by positivity
  filter_upwards [CompactGuardGrowth.eventually_guard_small (ε/((Nat.clog 2 c:ℝ)+20))
    (div_pos hε hden)] with n hn
  have h := reservation_bound c m n hm _ (div_pos hε hden) hn
  have he : ((Nat.clog 2 c:ℝ)+20)*(ε/((Nat.clog 2 c:ℝ)+20))=ε := by field_simp
  rwa [he] at h

theorem reservation_littleO_dimension (c m : ℕ) (hm : 2≤m) :
    (fun n : ℕ => (reserved c m n:ℝ)) =o[atTop] (fun n => (d n:ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [eventually_reservation_small c m hm ε hε] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hn

end
end IntegerMultBounds.Machine.CompactReservationGrowth
