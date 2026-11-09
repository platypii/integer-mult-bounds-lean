module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationPaddedVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication

/-! Price the exact-row dyadic transpose and prepared scatter by one padded
rectangle and ambient traffic; no numerical coefficient witnesses occur. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem exactDyadicPublicationCosts_le {s L : ℕ} (windows : PublicationWindows s L)
    (hL : 1 ≤ L) (hspan : L ≤ s) (b W oldVolume routeTime routeStock : ℕ) (hW : 1 ≤ W)
    (hOld : oldVolume ≤ 2^Nat.clog 2 windows.origins.length*(2^b*(L*W))) :
    let a := Nat.clog 2 windows.origins.length
    let bill := replicaPublicationCost (2^b) s (2^a-windows.origins.length) L W+37*s*W+6*(2^b)+31
    ((6*(2^(a+b)*(L*W))+4*oldVolume+4*(L*W)+9*(a+b)+14)+
      (26*(2^a*(2^b*(L*W)))+24+2*routeTime))+bill ≤
      400*(2^b*(s*W))+100+2*routeTime ∧
    ((2*(6*(2^(a+b)*(L*W))+4*oldVolume+4*(L*W)+9*(a+b)+14)+
      (40*(2^a*(2^b*(L*W)))+38+routeStock))+2*bill) ≤
      800*(2^b*(s*W))+200+routeStock := by
  dsimp only
  let a := Nat.clog 2 windows.origins.length
  let volume := 2^a*(2^b*(L*W))
  let traffic := 2^b*(s*W)
  let bill := replicaPublicationCost (2^b) s (2^a-windows.origins.length) L W+37*s*W+6*(2^b)+31
  have hpacket : 1 ≤ L*W := Nat.mul_pos hL hW
  have hreplicas : 1 ≤ 2^b := Nat.one_le_pow _ _ (by decide)
  have hcores : 1 ≤ 2^a := Nat.one_le_pow _ _ (by decide)
  have hpacketV : L*W ≤ volume := (Nat.le_mul_of_pos_left _ hreplicas).trans
    (Nat.le_mul_of_pos_left _ hcores)
  have hcoreV : 2^a ≤ volume := (Nat.le_mul_of_pos_right _ hreplicas).trans
    (by simpa only [volume,Nat.mul_assoc] using Nat.le_mul_of_pos_right (2^a*2^b) hpacket)
  have hreplicaV : 2^b ≤ volume := (Nat.le_mul_of_pos_right _ hpacket).trans
    (Nat.le_mul_of_pos_left _ hcores)
  have hab : a+b ≤ 2*volume := by
    have ha : a ≤ 2^a := Nat.lt_two_pow_self.le
    have hb : b ≤ 2^b := Nat.lt_two_pow_self.le
    omega
  have htraffic : s*W ≤ traffic := Nat.le_mul_of_pos_left _ hreplicas
  have hvolume : volume ≤ 3*traffic := by
    simpa only [volume,traffic,a,Nat.mul_assoc] using publicationPaddedVolume_le windows hspan b W
  have hpadding : (2^a-windows.origins.length)*L*W ≤ 2^a*(L*W) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (L*W) (Nat.sub_le (2^a) windows.origins.length)
  have hpadded := Nat.mul_le_mul_left (2^b) hpadding
  have hcost := PreparedPublicationPlan.replica_cost_le (2^b) s (2^a-windows.origins.length) L W
    (hL.trans hspan) hW
  have hbill : bill ≤ 21*volume+130*traffic+35 := by
    dsimp only [bill]
    dsimp only [volume,traffic] at htraffic ⊢
    nlinarith only [hcost,hpadded,htraffic]
  have hshape : 2^(a+b)*(L*W) = volume := by dsimp only [volume]; rw [pow_add,Nat.mul_assoc]
  change ((6*(2^(a+b)*(L*W))+4*oldVolume+4*(L*W)+9*(a+b)+14)+
      (26*volume+24+2*routeTime))+bill ≤ 400*traffic+100+2*routeTime ∧
    ((2*(6*(2^(a+b)*(L*W))+4*oldVolume+4*(L*W)+9*(a+b)+14)+
      (40*volume+38+routeStock))+2*bill) ≤ 800*traffic+200+routeStock
  rw [hshape]
  change oldVolume ≤ volume at hOld
  constructor <;> nlinarith only [hOld,hpacketV,hab,hvolume,hbill]

end IntegerMultBounds.MathlibTM2.Cost
