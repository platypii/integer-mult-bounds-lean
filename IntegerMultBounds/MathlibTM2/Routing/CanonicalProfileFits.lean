module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileSetup

/-! The existing canonical large-dimension gate supplies every numeric fit needed
by the compact fixed-bank profile compiler. No extra size threshold is imposed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

theorem canonicalProfileFits (L n : ℕ) (hn : n < 2 ^ L)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n)) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let w := canonicalStageWidths p
    0 < p.K ∧ p.wy < 2 ^ (w.indexBits + w.strideBits) ∧
      p.K < 2 ^ w.strideBits ∧ p.n < 2 ^ L ∧
      2 * (w.indexBits + w.strideBits) + 2 < 2 ^ L ∧
      w.strideBits < 2 ^ L ∧ p.K < 2 ^ L := by
  dsimp only
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have hgap := canonicalRouterGap_pos n
  have hcoord := canonicalDescriptorCoordinateWidth_le_gap n
  obtain ⟨hi, hg, hs, hsel, hw⟩ := canonicalStageWidths_router n hlarge r
  have hcoordWidth : (canonicalStageWidths p).indexBits + (canonicalStageWidths p).strideBits ≤
      canonicalRouterGap n := by
    dsimp only [p]
    rw [hi, hs]
    omega
  have hstride : canonicalRouterStride n = 64 * canonicalRouterGap n := rfl
  have hrows : p.n ≤ n := by
    change (n - canonicalRouterStride n) / (canonicalRouterStride n + 3 * canonicalRouterGap n) ≤ n
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hsource := canonicalStageWidths_source p
  change p.wy + 2 * p.wc + 0 <
    2 ^ ((canonicalStageWidths p).indexBits + (canonicalStageWidths p).strideBits) at hsource
  refine ⟨?_, ?_, canonicalStageWidths_key p, hrows.trans_lt hn, ?_, ?_, ?_⟩
  · change 0 < canonicalRouterStride n
    omega
  · dsimp only [p] at hsource ⊢
    omega
  · have hb : 2 * ((canonicalStageWidths p).indexBits + (canonicalStageWidths p).strideBits) + 2 ≤ n := by
      omega
    exact hb.trans_lt hn
  · have hb : (canonicalStageWidths p).strideBits ≤ n := by omega
    exact hb.trans_lt hn
  · change canonicalRouterStride n < 2 ^ L
    exact hlarge.trans_lt hn

end IntegerMultBounds.MathlibTM2.Routing
