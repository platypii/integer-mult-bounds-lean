module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPublicationDimensions
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublicationPaddedVolume

/-! Tight core capacity makes the complete unary dimension lifecycle linear
in ambient traffic, including the empty core class and metadata retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz PackedTranspose

theorem countedPublicationDimensionsCosts_le (N b s L W : ℕ)
    (hrows : N*L ≤ s) (hL : 1 ≤ L) (hspan : L ≤ s) (hs : 1 ≤ s) (hW : 1 ≤ W) :
    countedPublicationDimensionsCost b N L W+2*countedPublicationDimensionsVolume b N L W+15 ≤
      600*(2^b*(s*W)) ∧
    2*countedPublicationDimensionsCost b N L W ≤ 600*(2^b*(s*W)) := by
  let a := Nat.clog 2 N
  let C := 2^a
  let R := 2^b
  let traffic := R*(s*W)
  have hN : N ≤ C := Nat.le_pow_clog (by decide) N
  have hround : C ≤ 2*N+1 := pow_clog_two_le N
  have hCL : C*L ≤ 3*s := by nlinarith only [Nat.mul_le_mul_right L hround,hrows,hspan]
  have hCs : C ≤ 3*s := (Nat.le_mul_of_pos_right C hL).trans hCL
  have hsTraffic : s ≤ traffic := (Nat.le_mul_of_pos_right s hW).trans
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b))
  have htraffic : 1 ≤ traffic := hs.trans hsTraffic
  have hR : R ≤ traffic := Nat.le_mul_of_pos_right R (Nat.mul_pos hs hW)
  have hCTraffic : C ≤ 3*traffic := hCs.trans (Nat.mul_le_mul_left 3 hsTraffic)
  have hATraffic : a ≤ 3*traffic := Nat.lt_two_pow_self.le.trans hCTraffic
  have hb : b ≤ traffic := Nat.lt_two_pow_self.le.trans hR
  have hNTraffic : N ≤ traffic := ((Nat.le_mul_of_pos_right N hL).trans hrows).trans hsTraffic
  have hpacket : L*W ≤ traffic := (Nat.mul_le_mul_right W hspan).trans
    (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos b))
  have hLTraffic : L ≤ traffic := hspan.trans hsTraffic
  have hCLTraffic : C*L ≤ 3*traffic := hCL.trans (Nat.mul_le_mul_left 3 hsTraffic)
  have hmissing : (C-N)*L ≤ 3*traffic := (Nat.mul_le_mul_right L (Nat.sub_le C N)).trans hCLTraffic
  have hpad := paddingCounterSetupCost_le (width := L) hN
  have hpadTraffic : paddingCounterSetupCost N C L ≤ 63*traffic+18 := by
    nlinarith only [hpad,hCLTraffic,hCTraffic]
  have htime : countedPublicationDimensionsCost b N L W ≤ 232*traffic := by
    change ((19*R+10+(19*N+9))+(4*C+9*a+5))+
      PublicationDimensionReg.timeCost a b L W N C R ≤ _
    unfold PublicationDimensionReg.timeCost
    nlinarith only [hR,hNTraffic,hCTraffic,hATraffic,hb,hpacket,hLTraffic,hpadTraffic,htraffic]
  have hvolume : countedPublicationDimensionsVolume b N L W ≤ 16*traffic := by
    change 2*(a+b)+C+L*W+R+(C-N)*L ≤ _
    omega
  change _ ≤ 600*traffic ∧ _ ≤ 600*traffic
  constructor <;> omega

end IntegerMultBounds.MathlibTM2.Cost
