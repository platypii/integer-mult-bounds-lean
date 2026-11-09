module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedAllocatedPublication
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationMetadataCost
import Mathlib.Tactic.Linarith

/-! Structural bounds for the retained publication wrapper. Counter generation
and numerical handoff share one padded rectangle; coefficient data is absent. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem publicationRectangleCosts_le (a b N L W oldVolume : ℕ)
    (hfit : N ≤ 2^a) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hOld : oldVolume ≤ 2^a*2^b*(L*W)) :
    let volume := 2^a*2^b*(L*W)
    PublicationDimensionReg.timeCost a b L W N (2^a) (2^b) ≤ 100*volume+100 ∧
    PackedExactBatch.generatedOutputCopyTimeCost N (2^b) L W oldVolume ≤ 100*volume+20 ∧
    PackedExactBatch.generatedOutputCopyStock N (2^b) L W ≤ 100*volume+20 := by
  let volume := 2^a*2^b*(L*W)
  change oldVolume ≤ volume at hOld
  have hpacket : 1 ≤ L*W := Nat.mul_pos hL hW
  have hcapacity : 2^a ≤ volume :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b)).trans (Nat.le_mul_of_pos_right _ hpacket)
  have hreplicas : 2^b ≤ volume :=
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos a)).trans (Nat.le_mul_of_pos_right _ hpacket)
  have hpacketV : L*W ≤ volume := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.two_pow_pos a) (Nat.two_pow_pos b))
  have hrow : L ≤ volume := (Nat.le_mul_of_pos_right L hW).trans hpacketV
  have hcapacityL : 2^a*L ≤ volume := by
    have hh := Nat.le_mul_of_pos_right (2^a*L) (Nat.mul_pos (Nat.two_pow_pos b) hW)
    simpa only [volume,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  have hreplicaPacket : 2^b*(L*W) ≤ volume := by
    simpa only [volume,Nat.mul_assoc] using Nat.le_mul_of_pos_left (2^b*(L*W)) (Nat.two_pow_pos a)
  have hrows := hfit.trans hcapacity
  have hpayload : N*(2^b*(L*W)) ≤ volume := by
    simpa only [volume,Nat.mul_assoc] using Nat.mul_le_mul_right (2^b*(L*W)) hfit
  have ha : a ≤ volume := Nat.lt_two_pow_self.le.trans hcapacity
  have hb : b ≤ volume := Nat.lt_two_pow_self.le.trans hreplicas
  have hpadding := paddingCounterSetupCost_le (width := L) hfit
  have hsetup : PublicationDimensionReg.timeCost a b L W N (2^a) (2^b) ≤ 100*volume+100 := by
    unfold PublicationDimensionReg.timeCost
    nlinarith only [hpadding,ha,hb,hpacketV,hrow,hreplicas,hcapacityL,hcapacity]
  have hcopyTime : PackedExactBatch.generatedOutputCopyTimeCost N (2^b) L W oldVolume ≤ 100*volume+20 := by
    unfold PackedExactBatch.generatedOutputCopyTimeCost PackedExactBatch.copyWidthSetupCost reverseCopyRowsCost
    nlinarith only [hreplicaPacket,hreplicas,hrows,hpayload,hOld]
  have hcopyStock : PackedExactBatch.generatedOutputCopyStock N (2^b) L W ≤ 100*volume+20 := by
    unfold PackedExactBatch.generatedOutputCopyStock PackedExactBatch.copyWidthSetupCost reverseCopyRowsCost
    nlinarith only [hreplicaPacket,hreplicas,hrows,hpayload]
  exact ⟨hsetup,hcopyTime,hcopyStock⟩

theorem publicationControlWords_length_le {A s L : ℕ} (windows : PublicationWindows s L)
    (W : ℕ) (hW : 1 ≤ W) :
    (gatherControls A (windows.gaps W)).length ≤ 2*(s*W) := by
  have hv := windows.gaps_volume W
  have hc := windows.count_le
  have hs := Nat.le_mul_of_pos_right s hW
  simp only [scatterVolume,PublicationWindows.gaps_length] at hv
  simp only [length_gatherControls,PublicationWindows.gaps_length]
  omega


theorem retainedPublicationCosts_le {Q K s width : ℕ} [NeZero s] {U : Type}
    (hstates : FixedStreamedBank.stateCount ≤ Q) (a b L V W N : ℕ)
    (g : CorePublicationClass s width) (hw : 0 < width) (hL : L = g.length)
    (hspan : L ≤ s) (hpacket : 1 ≤ L) (hword : 1 ≤ W) (hfit : N ≤ 2^a)
    (oldVolume : ℕ) (hOld : oldVolume ≤ 2^a*2^b*(L*W)) :
    let volume := 2^a*2^b*(L*W)
    let pages := prepareReplicaPublicationPagesCost V s g.length W g.indices.length
    let pagesPush := mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q)
      (A := IntegerMultBounds.Networks.Shared50ModularControl.prime+K) (U := U))
    PackedTranspose.retainedPublicationTimeCost (K := K) hstates a b L V W N g hw oldVolume ≤
      500*volume+200*(2^b*(s*W))+100*V+500+pages+
        2*FixedStreamedBank.restoringTimeCost hstates a b (L*W) V ∧
    PackedTranspose.retainedPublicationStock (K := K) (U := U) hstates a b L V W N g ≤
      1000*volume+200*(2^b*(s*W))+200*V+800+pagesPush*pages+
        FixedStreamedBank.restoringStockAllowance hstates a b (L*W) V := by
  let volume := 2^a*2^b*(L*W)
  let pages := prepareReplicaPublicationPagesCost V s g.length W g.indices.length
  let pagesPush := mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q)
    (A := IntegerMultBounds.Networks.Shared50ModularControl.prime+K) (U := U))
  have hpacketPos : 1 ≤ L*W := Nat.mul_pos hpacket hword
  have hcapacity : 2^a ≤ volume :=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b)).trans (Nat.le_mul_of_pos_right _ hpacketPos)
  have hreplicas : 2^b ≤ volume :=
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos a)).trans (Nat.le_mul_of_pos_right _ hpacketPos)
  have hp : L*W ≤ volume := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.two_pow_pos a) (Nat.two_pow_pos b))
  have ha : a ≤ volume := Nat.lt_two_pow_self.le.trans hcapacity
  have hb : b ≤ volume := Nat.lt_two_pow_self.le.trans hreplicas
  have hrows : N*(2^b*(L*W)) ≤ volume := by
    simpa only [volume,Nat.mul_assoc] using Nat.mul_le_mul_right (2^b*(L*W)) hfit
  have hmissing : 2^b*((2^a-N)*L*W) ≤ volume := by
    have hh := Nat.mul_le_mul_right (2^b*(L*W)) (Nat.sub_le (2^a) N)
    simpa only [volume,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hh
  have hmissingL : (2^a-N)*L ≤ volume := by
    have hh := Nat.le_mul_of_pos_left ((2^a-N)*L*W) (Nat.two_pow_pos b)
    have hw := Nat.le_mul_of_pos_right ((2^a-N)*L) hword
    exact hw.trans (hh.trans hmissing)
  obtain ⟨hdim,hcopyTime,hcopyStock⟩ := publicationRectangleCosts_le a b N L W oldVolume hfit hpacket hword hOld
  change PublicationDimensionReg.timeCost a b L W N (2^a) (2^b) ≤ 100*volume+100 at hdim
  change PackedExactBatch.generatedOutputCopyTimeCost N (2^b) L W oldVolume ≤ 100*volume+20 at hcopyTime
  change PackedExactBatch.generatedOutputCopyStock N (2^b) L W ≤ 100*volume+20 at hcopyStock
  have hbinary : PublicationBinaryDimensions.timeCost a b (L*W) V ≤ 100*volume+40*V+100 := by
    unfold PublicationBinaryDimensions.timeCost
    omega
  have hmissingG : 2^b*((2^a-N)*g.length*W) ≤ volume := by
    simpa only [hL] using hmissing
  have hscatter := replicaPublicationCost_le (2^b) s (2^a-N) g.length W NeZero.one_le hword
  have hscatterBill : replicaPublicationCost (2^b) s (2^a-N) g.length W+6*(2^b)+6 ≤
      30*volume+87*(2^b*(s*W))+10 := by
    nlinarith only [hscatter,hmissingG,hreplicas]
  let windows := coreSubsetPublicationWindows s width g.length hw g.indices g.sublist
  have hcontrols := publicationControlWords_length_le (A := IntegerMultBounds.Networks.Shared50ModularControl.prime+K) windows W hword
  have hsource : s*W ≤ 2^b*(s*W) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b)
  have hpacketSource : g.length*W ≤ s*W := by
    simpa only [hL] using Nat.mul_le_mul_right W hspan
  have hretire : 2*(g.length*W+(gatherControls (IntegerMultBounds.Networks.Shared50ModularControl.prime+K)
      (windows.gaps W)).length)+5 ≤ 6*(2^b*(s*W))+5 := by
    omega
  dsimp only [windows] at hretire
  have hvolumeEq : 2^a*2^b*(L*W) = volume := rfl
  have ht : PackedTranspose.retainedPublicationTimeCost (K := K) hstates a b L V W N g hw oldVolume ≤
      500*volume+200*(2^b*(s*W))+100*V+500+pages+
        2*FixedStreamedBank.restoringTimeCost hstates a b (L*W) V := by
    unfold PackedTranspose.retainedPublicationTimeCost
    simp only [pow_add]
    dsimp only [pages,pagesPush]
    nlinarith only [hvolumeEq,hdim,hcopyTime,hbinary,hrows,hp,ha,hb,hreplicas,hmissingL,hscatterBill,hretire]
  have hs : PackedTranspose.retainedPublicationStock (K := K) (U := U) hstates a b L V W N g ≤
      1000*volume+200*(2^b*(s*W))+200*V+800+pagesPush*pages+
        FixedStreamedBank.restoringStockAllowance hstates a b (L*W) V := by
    unfold PackedTranspose.retainedPublicationStock
    simp only [pow_add]
    dsimp only [pages,pagesPush]
    nlinarith only [hvolumeEq,hdim,hcopyStock,hbinary,hrows,hp,ha,hb,hreplicas,hscatterBill,
      Nat.zero_le (2^b*(s*W))]
  exact ⟨ht,hs⟩

end IntegerMultBounds.MathlibTM2.Cost
