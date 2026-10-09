import IntegerMultBounds.Machine.CompactReservationPaddingHeaders
import IntegerMultBounds.Machine.CompactReservedVolumeBudget

/-! Paid adapter-header generation and erasure are uniformly charged to the
original native symbol volume, before the single global row pad. -/
namespace IntegerMultBounds.Machine.CompactReservationPaddingHeaderBudget
noncomputable section
open CompactReservationPaddingHeaders
open CompactGlobalRowHeaderOps
open CompactGlobalRowPadding

def constant (c m : ℕ) := 12000+RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)+
  RecursiveChildQuotientsConstant.cost 4+3*CompactGlobalRowHeaderPrimitives.logConstant m+
  FixedBasePowerDescriptor.constant c+FixedBasePowerDescriptor.constant 2

theorem rest_cost (c m D K rho ell q d G : ℕ) (hc : 0<c) :
    scheduleCost (rest c m) (CompactReservedHeaders.rowState c m D K rho ell q d G)=
      CompactGlobalRowHeaderPrimitives.logConstant m*d+FixedBasePowerDescriptor.constant c*(c^depth m d)+
      FixedBasePowerDescriptor.constant 2*originalRows c m d K+4096*initialRows c m d K+
      53*(rowAxes c m d*K+(D-rowAxes c m d)*K+D*K)+
      100*(D+rowAxes c m d+6*q+14*(D*K)+11)+RecursiveChildQuotientsConstant.cost 4+99 := by
  have hround := CompactRowPaddingRound.rounded_eq (originalRows c m d K) (c^depth m d)
    (pow_pos (by decide) _) (pow_pos hc _)
  dsimp [originalRows,depth] at hround
  dsimp [rest,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    CompactReservedHeaders.rowState,CompactReservedHeaders.initial,Function.update,depth,originalRows,initialRows]
  simp only [Option.getD_some]
  simp only [Nat.mul_comm] at hround ⊢
  rw [hround]
  ring

theorem cleanup_cost (c m D K rho ell q d G : ℕ) :
    scheduleCost cleanup (prepared c m D K rho ell q d G)=
      100*(rowAxes c m d+depth m d+c^depth m d+rowAxes c m d*K+originalRows c m d K+
        initialRows c m d K+(D-rowAxes c m d)+(D-rowAxes c m d)*K+D*K+width D K q+15)+11 := by
  simp [cleanup,cmd,scheduleCost,cost,eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,prepared,Function.update]
  ring

theorem linear (c m D K rho ell q d G V : ℕ) (hV : 0<V) (hc : 0<c)
    (hD : D≤V) (hd : d≤V) (hq : q≤V) (hB : D*K≤V) (hrow : rowAxes c m d≤V)
    (hlogc : Nat.clog 2 c≤V) (hlog : Nat.clog m (2*d)≤V) (hdepth : depth m d≤V)
    (hdiv : c^depth m d≤V) (hrbits : rowAxes c m d*K≤V)
    (hrows : originalRows c m d K≤V) (hpad : initialRows c m d K≤V)
    (hrest : (D-rowAxes c m d)*K≤V) (hw : width D K q≤V) :
    scheduleCost (schedule c m) (CompactReservedHeaders.initial D K rho ell q d G)+
      scheduleCost cleanup (prepared c m D K rho ell q d G)≤constant c m*V := by
  rw [schedule,scheduleCost_append,CompactReservedHeaders.row_executes,rest_cost c m D K rho ell q d G hc,cleanup_cost,
    CompactReservedHeaderBudget.row_cost]
  have hdiff : D-rowAxes c m d≤V := (Nat.sub_le _ _).trans hD
  have hp0 := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant c) hdiv
  have hp1 := Nat.mul_le_mul_left (FixedBasePowerDescriptor.constant 2) hrows
  have hl := Nat.mul_le_mul_left (CompactGlobalRowHeaderPrimitives.logConstant m) hd
  have hf0 := Nat.le_mul_of_pos_right (RecursiveChildQuotientsConstant.cost (Nat.clog 2 c)) hV
  have hf1 := Nat.le_mul_of_pos_right (RecursiveChildQuotientsConstant.cost 4) hV
  unfold constant
  nlinarith

theorem cost_linear (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hres : CompactReservedHeaders.reserved c m d G K≤D) :
    scheduleCost (schedule c m) (CompactReservedHeaders.initial D K rho ell q d G)+
      scheduleCost cleanup (prepared c m D K rho ell q d G)≤
        constant c m*CompactFallbackAxisRun.volume D K ell q := by
  let V := CompactFallbackAxisRun.volume D K ell q
  have hgeom := CompactReservedVolumeBudget.geometry c m D K d G hd hG hK hres
  have hDpos := hgeom.2.1
  have hrowD : rowAxes c m d≤D := by
    unfold CompactReservedHeaders.reserved CompactReservedHeaders.high at hres
    omega
  have hback : CompactGadgetReservationCapacity.backChunks d G K≤D := by
    unfold CompactReservedHeaders.reserved at hres
    omega
  have hcap := (CompactGadgetReservationCapacity.capacities d G K hK).2
  change d*G≤CompactGadgetReservationCapacity.backChunks d G K*K at hcap
  have hdB : d≤D*K := (Nat.le_mul_of_pos_right d hG).trans
    (hcap.trans (Nat.mul_le_mul_right K hback))
  have hR : 0<(2:ℕ)^ell := pow_pos (by decide) _
  have hP : 0<(2:ℕ)^(D*K) := pow_pos (by decide) _
  have hv : V=2^(D*K)*2^ell*(2*(width D K q+1)) := by
    unfold V CompactFallbackAxisRun.volume ButterflyAxisHeadersBudget.logicalVolume
      CompactFallbackHeaders.bits CompactFallbackHeaders.polynomials ButterflyAxisHeadersData.recordLength
      ButterflyAxisHeadersData.width CompactFallbackHeaders.reservation width
    unfold CompactFallbackHeaders.bits
    ring
  have hV : 0<V := by rw [hv]; positivity
  have hrecord : 2*(width D K q+1)≤V := by
    rw [hv]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hP hR)
  have hB : D*K≤V := by unfold width at hrecord; omega
  have hD : D≤V := (Nat.le_mul_of_pos_right D hK).trans hB
  have hrow : rowAxes c m d≤V := hrowD.trans hD
  have hlogcpos := CompactGlobalRowHeaders.logc_positive c hc
  have hlogpos : 0<Nat.clog m (2*d) := by
    have hh := Nat.le_pow_clog (by omega : 1<m) (2*d)
    by_contra hh0
    have he : Nat.clog m (2*d)=0 := by omega
    simp only [he,pow_zero] at hh
    omega
  have hlc : Nat.clog 2 c≤V := (Nat.le_mul_of_pos_right _ hlogpos).trans hrow
  have hlog : Nat.clog m (2*d)≤V := (Nat.le_mul_of_pos_left _ hlogcpos).trans hrow
  have hdepth : depth m d≤V := (Nat.clog_mono_right m (show d≤2*d by omega)).trans hlog
  have hrbits : rowAxes c m d*K≤V := (Nat.mul_le_mul_right K hrowD).trans hB
  have hrowsP : originalRows c m d K≤2^(D*K) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right K hrowD)
  have htworows : 2*originalRows c m d K≤V := by
    have hm0 := Nat.mul_le_mul_left 2 hrowsP
    have hm1 := Nat.mul_le_mul_left (2*(2:ℕ)^(D*K)) (show 1≤2^ell from hR)
    have hm2 := Nat.mul_le_mul_left ((2:ℕ)^(D*K)*2^ell)
      (show 2≤2*(width D K q+1) by omega)
    rw [hv]
    nlinarith
  have hrows : originalRows c m d K≤V := by omega
  have hpad := (initial_bounds c m d K (by omega) hK).2.2.1.trans htworows
  have hdiv := (divisor_le_original c m d K hK).trans hrows
  have hrest := (Nat.mul_le_mul_right K (Nat.sub_le D (rowAxes c m d))).trans hB
  have hq : q≤V := by unfold width at hrecord; omega
  have hw : width D K q≤V := by omega
  exact linear c m D K rho ell q d G V hV (by omega) hD (hdB.trans hB) hq hB hrow
    hlc hlog hdepth hdiv hrbits hrows hpad hrest hw

end
end IntegerMultBounds.Machine.CompactReservationPaddingHeaderBudget
