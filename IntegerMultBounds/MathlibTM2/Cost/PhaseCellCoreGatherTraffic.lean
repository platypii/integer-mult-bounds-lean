module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRealGatherTraffic

/-! Amortize the actual per-replica gather controller against core width.
Only padded payload volume remains in addition to linear ambient traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem replicaCoreGatherStepCost_eq (V s width radius L w : ℕ) :
    replicaCoreGatherStepCost V s width radius L w =
      (18*((s+width-1)/width)+9+3*(coreGatherIndices s width radius L).length)*tblC V V+
      (coreGatherIndices s width radius L).length*(14*(L*w)+39*V+65)+
      38*(s*w)+6*(L*w)+w*(4*V+10)+267*V+17*L+376 := by
  unfold replicaCoreGatherStepCost restoredCoreGatherCost initializedCoreGatherCost preparedOriginAdvanceCost
  ring

def coreGatherTrafficFactor (cV cW : ℕ) : ℕ := 431+41683*cV^2+4*cW*cV+10*cW

theorem replicaCoreGatherStepCost_le (cV cW p V s width radius L w capacity : ℕ)
    (hVpos : 1 ≤ V) (hs : 1 ≤ s) (hw : 1 ≤ w) (hwidth : 0 < width)
    (hwidthS : width ≤ s) (hprepare : p^2 ≤ width) (hL : L ≤ s)
    (hV : V ≤ cV*p) (hW : w ≤ cW*p) (hcapacity : 1 ≤ capacity)
    (hrows : (coreGatherIndices s width radius L).length ≤ capacity) :
    replicaCoreGatherStepCost V s width radius L w ≤
      coreGatherTrafficFactor cV cW*(s*w)+20*(capacity*(L*w)) := by
  let q := (s+width-1)/width
  let J := (coreGatherIndices s width radius L).length
  have hJ : J ≤ q := by
    exact (List.length_filter_le ..).trans (by simp [coreIndices,q])
  have hq : q*width ≤ 2*s := by
    have hh := Nat.div_mul_le_self (s+width-1) width
    dsimp only [q]
    omega
  have hpS : p^2 ≤ s := hprepare.trans hwidthS
  have hVSq : V^2 ≤ cV^2*width := by
    have hh := Nat.pow_le_pow_left hV 2
    have hm := Nat.mul_le_mul_left (cV^2) hprepare
    nlinarith only [hh,hm]
  have hVS : V^2 ≤ cV^2*s := hVSq.trans (Nat.mul_le_mul_left _ hwidthS)
  have hqV : q*V^2 ≤ 2*cV^2*s := by
    have h₁ := Nat.mul_le_mul_left q hVSq
    have h₂ := Nat.mul_le_mul_left (cV^2) hq
    nlinarith only [h₁,h₂]
  have hVUnit : V ≤ V^2 := Nat.le_self_pow (by decide) V
  have hV1 : 1 ≤ V^2 := hVpos.trans hVUnit
  have htbl : tblC V V ≤ 808*V^2 := by
    unfold tblC
    nlinarith only [hVUnit,hV1]
  have hcoeff : 18*q+9+3*J ≤ 21*q+9 := by omega
  have htable := Nat.mul_le_mul hcoeff htbl
  have hcontrol := Nat.mul_le_mul hJ (show 39*V+65 ≤ 104*V^2 by nlinarith only [hVUnit,hV1])
  have hpacket := Nat.mul_le_mul_right (L*w) hrows
  have hsinglePacket : L*w ≤ capacity*(L*w) := Nat.le_mul_of_pos_left _ (by omega)
  have hwordProduct : w*V ≤ cW*cV*s := by
    have h₁ := Nat.mul_le_mul hW hV
    have h₂ := Nat.mul_le_mul_left (cW*cV) hpS
    nlinarith only [h₁,h₂]
  have hword : w ≤ cW*s := hW.trans (Nat.mul_le_mul_left cW
    ((Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) p).trans hpS))
  have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hw
  have hsw1 : 1 ≤ s*w := hs.trans hsw
  have hLw : L ≤ s*w := hL.trans hsw
  have hfixed : (41683*cV^2+4*cW*cV+10*cW)*s ≤
      (41683*cV^2+4*cW*cV+10*cW)*(s*w) := Nat.mul_le_mul_left _ hsw
  rw [replicaCoreGatherStepCost_eq]
  dsimp only [coreGatherTrafficFactor,q,J] at htable hcontrol hqV hpacket ⊢
  nlinarith only [htable,hcontrol,hqV,hVS,hpacket,hsinglePacket,hwordProduct,hword,
    hVUnit,hLw,hsw1,hfixed]

variable {t₀ T Q c d W K : ℕ}
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem realGatherTimeCost_le_linear (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B C : ℕ) (S : Stacks T (prime+K))
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c) (hreplicas : B = 2^d)
    (hsw : 1 ≤ s*w)
    (hstep : replicaCoreGatherStepCost V s width radius L w ≤ C*(s*w)+20*((2^d)^c*(L*w))) :
    plan.realGatherTimeCost V s width radius L w B S ≤ plan.inverseCost S+
      6*((2^d)^c*(L*w))+34*(2^d)^c+64+B*((C+29)*(s*w)+42*((2^d)^c*(L*w))) := by
  have h := realGatherTimeCost_le plan V s width radius L w B S hcapacity hreplicas
  have hcap : 1 ≤ (2^d)^c := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))
  have hpacket : L*w ≤ (2^d)^c*(L*w) := Nat.le_mul_of_pos_left _ (by omega)
  have hrow : replicaCoreGatherStepCost V s width radius L w+2*(s*w)+
      16*((2^d)^c*(L*w))+6*(L*w)+27 ≤ (C+29)*(s*w)+42*((2^d)^c*(L*w)) := by
    nlinarith only [hstep,hpacket,hsw]
  nlinarith only [h,Nat.mul_le_mul_left B hrow]

theorem realGatherStockAllowance_le_linear (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B C : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c) (hreplicas : B = 2^d)
    (hsw : 1 ≤ s*w)
    (hstep : replicaCoreGatherStepCost V s width radius L w ≤ C*(s*w)+20*((2^d)^c*(L*w))) :
    plan.realGatherStockAllowance V s width radius L w B ≤ plan.inverseStockAllowance+
      3*C*(s*w)+76*((2^d)^c*(L*w))+68*(2^d)^c+122+B*(33*((2^d)^c*(L*w))+18*(s*w)) := by
  have h := realGatherStockAllowance_le plan V s width radius L w B hcapacity hreplicas
  have hcap : 1 ≤ (2^d)^c := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide : 1 ≤ 2))
  have hpacket : L*w ≤ (2^d)^c*(L*w) := Nat.le_mul_of_pos_left _ (by omega)
  have hrow : 21*((2^d)^c*(L*w))+12*(L*w)+18 ≤ 33*((2^d)^c*(L*w))+18*(s*w) := by
    nlinarith only [hpacket,hsw]
  nlinarith only [h,hstep,Nat.mul_le_mul_left B hrow]

/-- A geometric padding bound is the remaining gate for linear exposure
traffic. It is not implied merely by fitting the real rows in the archive. -/
theorem realGatherTimeCost_le_volume (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B C cPad : ℕ) (S : Stacks T (prime+K))
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c) (hreplicas : B = 2^d)
    (hsw : 1 ≤ s*w) (hpacket : 1 ≤ L*w) (hpad : (2^d)^c*L ≤ cPad*s)
    (hstep : replicaCoreGatherStepCost V s width radius L w ≤ C*(s*w)+20*((2^d)^c*(L*w))) :
    plan.realGatherTimeCost V s width radius L w B S ≤ plan.inverseCost S+
      (40*cPad+64+B*(C+29+42*cPad))*(s*w) := by
  have h := realGatherTimeCost_le_linear plan V s width radius L w B C S hcapacity hreplicas hsw hstep
  have hpadded : (2^d)^c*(L*w) ≤ cPad*(s*w) := by
    nlinarith only [Nat.mul_le_mul_right w hpad]
  have hrows : (2^d)^c ≤ (2^d)^c*(L*w) := by simpa using Nat.mul_le_mul_left ((2^d)^c) hpacket
  have hrep := Nat.mul_le_mul_left (42*B) hpadded
  nlinarith only [h,hpadded,hrows,hsw,hrep]

theorem realGatherStockAllowance_le_volume (plan : ArchiveTilePlan t₀ T Q c d W)
    (V s width radius L w B C cPad : ℕ)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c) (hreplicas : B = 2^d)
    (hsw : 1 ≤ s*w) (hpacket : 1 ≤ L*w) (hpad : (2^d)^c*L ≤ cPad*s)
    (hstep : replicaCoreGatherStepCost V s width radius L w ≤ C*(s*w)+20*((2^d)^c*(L*w))) :
    plan.realGatherStockAllowance V s width radius L w B ≤ plan.inverseStockAllowance+
      (3*C+144*cPad+122+B*(33*cPad+18))*(s*w) := by
  have h := realGatherStockAllowance_le_linear plan V s width radius L w B C hcapacity hreplicas hsw hstep
  have hpadded : (2^d)^c*(L*w) ≤ cPad*(s*w) := by
    nlinarith only [Nat.mul_le_mul_right w hpad]
  have hrows : (2^d)^c ≤ (2^d)^c*(L*w) := by simpa using Nat.mul_le_mul_left ((2^d)^c) hpacket
  have hrep := Nat.mul_le_mul_left (33*B) hpadded
  nlinarith only [h,hpadded,hrows,hsw,hrep]

end IntegerMultBounds.MathlibTM2.Cost
