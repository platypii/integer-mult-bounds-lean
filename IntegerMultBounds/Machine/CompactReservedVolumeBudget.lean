import IntegerMultBounds.Machine.CompactReservedHeaderBudget

/-! All derived controls are bounded by the actual binary address dimension.
Their quadratic descriptor work is absorbed by the existing native volume;
no new coefficient coordinates or width conversion are charged implicitly. -/
namespace IntegerMultBounds.Machine.CompactReservedVolumeBudget
noncomputable section
open CompactReservedHeaders
open CompactReservedHeaderBudget (scalar)
open CompactFallbackHeaders (bits polynomials reservation)
open CompactFallbackAxisRun (volume Array Width word)
open CompactGadgetReservationCapacity (backChunks frontChunks)

theorem geometry (c m D K d G : ℕ) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hres : reserved c m d G K≤D) :
    0<reserved c m d G K ∧ 0<D ∧ scalar c m D K d G≤5*(bits D K+1) := by
  have hcap := (CompactGadgetReservationCapacity.capacities d G K hK).2
  change d*G≤backChunks d G K*K at hcap
  have hback : backChunks d G K≤D := by unfold reserved at hres; omega
  have hrow : CompactGlobalRowPadding.rowAxes c m d≤D := by unfold reserved high at hres; omega
  have hp : 0<d*G := Nat.mul_pos hd hG
  have hb : 0<backChunks d G K := by nlinarith
  have hr : 0<reserved c m d G K := by unfold reserved; omega
  have hD : 0<D := by omega
  have hcapD : d*G≤D*K := hcap.trans (Nat.mul_le_mul_right K hback)
  have hdG : d≤d*G := Nat.le_mul_of_pos_right _ hG
  have hDB : D≤D*K := Nat.le_mul_of_pos_right _ hK
  have hKB : K≤D*K := Nat.le_mul_of_pos_left _ hD
  refine ⟨hr,hD,?_⟩
  unfold scalar bits
  omega

theorem dimension_square_le (D K ell q : ℕ) : (bits D K+1)^2≤volume D K ell q := by
  have hp : bits D K+1≤2^(bits D K) := Nat.lt_two_pow_self
  have hR : 1≤polynomials ell := Nat.one_le_two_pow
  have hr : bits D K+1≤ButterflyAxisHeadersData.recordLength (bits D K) (reservation D K q) := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width reservation
    omega
  have hm := Nat.mul_le_mul hp hr
  have hmul := Nat.mul_le_mul_right
    (ButterflyAxisHeadersData.recordLength (bits D K) (reservation D K q)) (Nat.mul_le_mul_left (2^(bits D K)) hR)
  unfold volume ButterflyAxisHeadersBudget.logicalVolume
  nlinarith

theorem scalar_square_le (c m D K ell q d G : ℕ) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hres : reserved c m d G K≤D) :
    (scalar c m D K d G)^2≤25*volume D K ell q := by
  have hs := (geometry c m D K d G hd hG hK hres).2.2
  have hv := dimension_square_le D K ell q
  nlinarith

theorem lifecycle_cost (c m D K rho ell q d G : ℕ) (hres : reserved c m d G K≤D) :
    CompactChildHeadersArithmetic.scheduleCost CompactReservedLifecycle.switch
      (prepared c m D K rho ell q d G (backChunks d G K))+
    CompactChildHeadersArithmetic.scheduleCost CompactReservedLifecycle.cleanup
      (prepared c m D K rho ell q d G D)+4≤1000*(scalar c m D K d G)^2 := by
  have hb : backChunks d G K≤D := by unfold reserved at hres; omega
  have hh : high c m d G K≤D := by unfold reserved at hres; omega
  have hs : D-high c m d G K≤D := Nat.sub_le _ _
  have hD : D+1≤scalar c m D K d G := by unfold scalar; omega
  simp [CompactReservedLifecycle.switch,CompactReservedLifecycle.cleanup,
    CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
    ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    prepared,Function.update]
  nlinarith

def constant (c m : ℕ) := CompactFallbackAxisBudget.constant+25*CompactReservedHeaderBudget.constant c m+25109

theorem cost_linear (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hres : reserved c m d G K≤D) :
    CompactReservedOriginal.cost c m D K rho ell q d G≤
      constant c m*volume D K ell q*reserved c m d G K := by
  have hg := geometry c m D K d G hd hG hK hres
  have hs := scalar_square_le c m D K ell q d G hd hG hK hres
  have h0 := (CompactReservedHeaderBudget.setup_cost c m D K rho ell q d G hc).trans
    (Nat.mul_le_mul_left (CompactReservedHeaderBudget.constant c m) hs)
  have h1 := (lifecycle_cost c m D K rho ell q d G hres).trans (Nat.mul_le_mul_left 1000 hs)
  have hb := ActiveRepairRankHeadersCommands.bits_length (backChunks d G K)
  have hh := ActiveRepairRankHeadersCommands.bits_length (high c m d G K)
  have hV : 0<volume D K ell q := ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell)
  have hNV : reserved c m d G K≤volume D K ell q*reserved c m d G K := Nat.le_mul_of_pos_left _ hV
  have hVN : volume D K ell q≤volume D K ell q*reserved c m d G K := Nat.le_mul_of_pos_right _ hg.1
  have hsetup := Nat.mul_le_mul_left (25*CompactReservedHeaderBudget.constant c m) hVN
  unfold CompactReservedOriginal.cost CompactReservedSchedule.cost constant
  unfold reserved at hNV hVN hsetup
  nlinarith

theorem runs_linear (inverse : Bool) (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K) (hr : rho<K) (hres : reserved c m d G K≤D)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime (CompactReservedOriginal.program inverse c m)
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G) (word f))
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G)
        (word (CompactReservedOriginal.result inverse c m D K rho ell q d G f)))
      (constant c m*volume D K ell q*reserved c m d G K) :=
  (CompactReservedOriginal.runs inverse c m D K rho ell q d G hc hm hd hK hr hres f hw).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear c m D K rho ell q d G hc hd hG hK hres)

/-- The second complete header lifecycle and sequence jump are also paid. -/
theorem roundtrip_cost_linear (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hres : reserved c m d G K≤D) :
    CompactReservedRoundtrip.cost c m D K rho ell q d G≤
      (2*constant c m+1)*volume D K ell q*reserved c m d G K := by
  have hh := cost_linear c m D K rho ell q d G hc hd hG hK hres
  have hp : 0<volume D K ell q*reserved c m d G K := Nat.mul_pos
    (ButterflyAxisHeadersInstall.volume_pos _ _ _ (pow_pos (by decide) ell))
    (geometry c m D K d G hd hG hK hres).1
  unfold CompactReservedRoundtrip.cost
  nlinarith

end
end IntegerMultBounds.Machine.CompactReservedVolumeBudget
