module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryLocalVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreActiveVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreLocalStock

/-! Full recovery volume summed over the actual core-halo geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open scoped BigOperators

def haloRecoveryLocalVolume (p s t band a b : ℕ) [NeZero s] : ℕ :=
  haloLocalNativeVolume s t band a b 1+p^2+(b-a)+band+
    (haloBoundary s t band a b).card+1+
    ((haloBoundary s t band a b).card+1)*(12*band+1)+
    (retainedCouplingActiveRows true s t band a b a (b-a)+
      retainedCouplingActiveRows false s t band a b a (b-a))*(2*band+1)

theorem replicaRecoveryLocalVolume_eq_halo {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaRecoveryLocalVolume H = haloRecoveryLocalVolume H.p s H.t H.band H.origin (H.origin+H.span) := by
  simp only [replicaRecoveryLocalVolume,haloRecoveryLocalVolume,replicaHaloLocalCoordinates,
    haloLocalNativeVolume,Nat.add_sub_cancel_left,Nat.mul_one]

/-- Summed boundary solves retain sparse ambient phase cuts and short guards. -/
theorem coreHalo_boundaryWork_sum_le {s t : ℕ} [NeZero s] (hst : s < t)
    (width band n : ℕ) (hw : 0 < width) (hr : n*band ≤ width) (hband : 1 ≤ band) :
    (∑ k ∈ (coreIndices s width).toFinset,
      ((haloBoundary s t band (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2).card+1)*(12*band+1)) ≤
      312*(t-s)*band^2+39*(coreIndices s width).length*band^2 := by
  let K := (coreIndices s width).toFinset
  let rows := fun k => (haloBoundary s t band (coreHaloEndpoints s width k band n).1
    (coreHaloEndpoints s width k band n).2).card
  have hs := coreHalo_boundary_volume_le (s := s) t width band n band hw hr
  have hc := boundary_card s t hst band (interiorSet s t band) (fun j => mem_interiorSet band j)
  have hg : 1 ≤ t-s := by omega
  have hcount : (∑ k ∈ K, rows k)+K.card ≤ 24*band*(t-s)+3*band*(coreIndices s width).length := by
    change (∑ k ∈ K, rows k) ≤ _ at hs
    have hh : band ≤ band*(t-s) := Nat.le_mul_of_pos_right _ hg
    have hK : K.card = (coreIndices s width).length := List.toFinset_card_of_nodup (coreIndices_nodup s width)
    have hguard := Nat.mul_le_mul_right (coreIndices s width).length hband
    nlinarith only [hs,hc,hh,hK,hguard]
  have hwidth : 12*band+1 ≤ 13*band := by omega
  calc
    _ = ((∑ k ∈ K, rows k)+K.card)*(12*band+1) := by
      change (∑ k ∈ K, (rows k+1)*(12*band+1)) = _
      rw [←Finset.sum_mul]
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.mul_one,Nat.cast_id]
    _ ≤ (24*band*(t-s)+3*band*(coreIndices s width).length)*(13*band) := Nat.mul_le_mul hcount hwidth
    _ = _ := by ring

/-- All local bills, before absorbing the per-core scalar and guard overhead. -/
theorem coreHalo_recoveryLocalVolume_sum_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p width band n : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hr : n*band ≤ width) (hband : 1 ≤ band) (hcell : s/(t-s)+1 ≤ width) :
    (∑ k ∈ (coreIndices s width).toFinset,
      haloRecoveryLocalVolume p s t band (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2) ≤
      200*s+600*(t-s)*band^2+100*(coreIndices s width).length*(p^2+band^2) := by
  let K := (coreIndices s width).toFinset
  let a := fun k => (coreHaloEndpoints s width k band n).1
  let b := fun k => (coreHaloEndpoints s width k band n).2
  let span := fun k => b k-a k
  let rows := fun k => (haloBoundary s t band (a k) (b k)).card
  let active := fun boundary k => retainedCouplingActiveRows boundary s t band (a k) (b k) (a k) (span k)
  have hnative : (∑ k ∈ K, haloLocalNativeVolume s t band (a k) (b k) 1) ≤ 163*s := by
    simpa only [Nat.mul_one] using coreHalo_localNativeVolume_le t width band n 1 hw hwidth hr hcell (by decide)
  have hspan : (∑ k ∈ K, span k) ≤ 9*s := coreHaloEndpoints_span_volume_le width band n hwidth hr
  have hrows : (∑ k ∈ K, rows k) ≤ 9*s := by
    apply le_trans (Finset.sum_le_sum (s := K) (g := span) ?_) hspan
    intro k _
    exact (Finset.card_le_card (Finset.sdiff_subset : haloBoundary s t band (a k) (b k) ⊆
      haloVertices s (a k) (b k))).trans (haloVertices_card_le s (a k) (b k))
  have hboundary := coreHalo_boundaryWork_sum_le hst width band n hw hr hband
  have htrue := coreHalo_activeWork_sum_le hst width band n hw hr hband true
  have hfalse := coreHalo_activeWork_sum_le hst width band n hw hr hband false
  have hK : K.card = (coreIndices s width).length := List.toFinset_card_of_nodup (coreIndices_nodup s width)
  have heq (k : ℕ) : haloRecoveryLocalVolume p s t band (a k) (b k) =
      haloLocalNativeVolume s t band (a k) (b k) 1+span k+rows k+(p^2+band+1)+
        (rows k+1)*(12*band+1)+active true k*(2*band+1)+active false k*(2*band+1) := by
    unfold haloRecoveryLocalVolume
    dsimp only [span,rows,active]
    ring
  have hs : (∑ k ∈ K, haloRecoveryLocalVolume p s t band (a k) (b k)) =
      (∑ k ∈ K, haloLocalNativeVolume s t band (a k) (b k) 1)+(∑ k ∈ K, span k)+
        (∑ k ∈ K, rows k)+K.card*(p^2+band+1)+
        (∑ k ∈ K, (rows k+1)*(12*band+1))+
        (∑ k ∈ K, active true k*(2*band+1))+(∑ k ∈ K, active false k*(2*band+1)) := by
    simp_rw [heq,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
    ring
  have hb2 : band+1 ≤ 2*band^2 := by
    have hh : band ≤ band^2 := Nat.le_self_pow (by decide) band
    omega
  have hguard := Nat.mul_le_mul_left K.card hb2
  change (∑ k ∈ K, (rows k+1)*(12*band+1)) ≤ _ at hboundary
  change (∑ k ∈ K, active true k*(2*band+1)) ≤ _ at htrue
  change (∑ k ∈ K, active false k*(2*band+1)) ≤ _ at hfalse
  change (∑ k ∈ K, haloRecoveryLocalVolume p s t band (a k) (b k)) ≤ _
  nlinarith only [hs,hnative,hspan,hrows,hboundary,htrue,hfalse,hK,hguard,
    Nat.zero_le (K.card*p^2)]

/-- A core wide enough for scalar preparation and short guards pays one global
local-volume bill, with no extra core-count factor. -/
theorem coreHalo_recoveryLocalVolume_amortized_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p width band n : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hr : n*band ≤ width) (hband : 1 ≤ band) (hcell : s/(t-s)+1 ≤ width)
    (hprepare : p^2+band^2 ≤ width) :
    (∑ k ∈ (coreIndices s width).toFinset,
      haloRecoveryLocalVolume p s t band (coreHaloEndpoints s width k band n).1
        (coreHaloEndpoints s width k band n).2) ≤ 600*(s+(t-s)*band^2) := by
  have hs := coreHalo_recoveryLocalVolume_sum_le hst p width band n hw hwidth hr hband hcell
  have hg := (Nat.mul_le_mul_left (coreIndices s width).length hprepare).trans
    (coreSlots_le_two s width hwidth)
  nlinarith only [hs,hg,Nat.zero_le s]

/-- The geometric bound applies directly to actual numerical problems at each
core endpoint; solutions, precision and numerical data need no comparison. -/
theorem coreReplicaRecoveryLocalVolume_amortized_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p width band n : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hr : n*band ≤ width) (hband : 1 ≤ band) (hcell : s/(t-s)+1 ≤ width)
    (hprepare : p^2+band^2 ≤ width) (H : ℕ → ReplicaHaloProblem s)
    (hparams : ∀ k ∈ coreIndices s width, (H k).p = p ∧ (H k).t = t ∧ (H k).band = band ∧
      (H k).origin = (coreHaloEndpoints s width k band n).1 ∧
      (H k).span = (coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1) :
    (∑ k ∈ (coreIndices s width).toFinset, replicaRecoveryLocalVolume (H k)) ≤
      600*(s+(t-s)*band^2) := by
  calc
    _ = ∑ k ∈ (coreIndices s width).toFinset,
        haloRecoveryLocalVolume p s t band (coreHaloEndpoints s width k band n).1
          (coreHaloEndpoints s width k band n).2 := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨hp,ht,hB,ha,hspan⟩ := hparams k (List.mem_toFinset.mp hk)
      rw [replicaRecoveryLocalVolume_eq_halo,hp,ht,hB,ha,hspan,
        Nat.add_sub_of_le (coreHaloEndpoints_bounds s width k band n).1]
    _ ≤ _ := coreHalo_recoveryLocalVolume_amortized_le hst p width band n hw hwidth hr hband hcell hprepare

theorem amortizedCoreWidth_preparation_le (ct p u : ℕ) (hp : 1 ≤ p) :
    p^2+(PhaseCellBand.width p u)^2 ≤ amortizedCoreWidth ct p ∧
      5*p ≤ amortizedCoreWidth ct p := by
  have hband : PhaseCellBand.width p u ≤ 17*p := by
    have hs := Nat.sqrt_le_self (16*p/u)
    have hd := Nat.div_le_self (16*p) u
    unfold PhaseCellBand.width
    omega
  have hb := Nat.mul_le_mul hband hband
  have hb2 : (PhaseCellBand.width p u)^2 ≤ 289*p^2 := by nlinarith only [hb]
  have hp28 : p^2 ≤ p^8 := Nat.pow_le_pow_right hp (by decide)
  have hp8 : p ≤ p^8 := Nat.le_self_pow (by decide) p
  have hcoeff : 290 ≤ 816*(ct+5)+18 := by omega
  constructor
  · calc
      _ ≤ 290*p^2 := by omega
      _ ≤ 290*p^8 := Nat.mul_le_mul_left _ hp28
      _ ≤ (816*(ct+5)+18)*p^8 := Nat.mul_le_mul_right _ hcoeff
      _ = _ := rfl
  · have h₁ := Nat.mul_le_mul_left 5 hp8
    have h₂ := Nat.mul_le_mul_right (p^8) (show 5 ≤ 816*(ct+5)+18 by omega)
    exact h₁.trans h₂

/-- The selected wider cores discharge every local-volume amortization premise. -/
theorem selectedCoreRecoveryLocalVolume_sum_le (ct : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (u target : ℕ), target ≤ ct*Sizes.p n →
      (∑ k ∈ (coreIndices (Sizes.s n i) (amortizedCoreWidth ct (Sizes.p n))).toFinset,
        haloRecoveryLocalVolume (Sizes.p n) (Sizes.s n i) (Sizes.t n i)
          (PhaseCellBand.width (Sizes.p n) u)
          (coreHaloEndpoints (Sizes.s n i) (amortizedCoreWidth ct (Sizes.p n)) k
            (PhaseCellBand.width (Sizes.p n) u) (localityDepth (Sizes.p n) target)).1
          (coreHaloEndpoints (Sizes.s n i) (amortizedCoreWidth ct (Sizes.p n)) k
            (PhaseCellBand.width (Sizes.p n) u) (localityDepth (Sizes.p n) target)).2) ≤
        600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*(PhaseCellBand.width (Sizes.p n) u)^2) := by
  filter_upwards [selectedAmortizedCoreGeometry ct] with n hn
  intro h i _ u target htarget
  obtain ⟨hw,_,hr,hroom,_⟩ := hn h i u target htarget
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  obtain ⟨hprepare,hpadding⟩ := amortizedCoreWidth_preparation_le ct (Sizes.p n) u hp
  have hcell := phaseGap_cellLength_le hp (h.good.lt i) (h.quarter_p_le_theta i)
  apply coreHalo_recoveryLocalVolume_amortized_le (h.good.lt i) _ _ _ _ hw (by omega) hr
    (PhaseCellBand.width_pos _ _) (by omega) hprepare

end IntegerMultBounds.MathlibTM2.Cost
