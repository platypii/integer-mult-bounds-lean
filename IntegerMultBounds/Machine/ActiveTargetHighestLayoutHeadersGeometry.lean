import IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersRun
import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersGeometry

/-! The physically synthesized five words are the exact unchanged-layout
highest-pair geometry for either source order. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersGeometry
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes (Parameters)
open ActivePrefixLayoutHeadersGeometry (inputs)
open ActiveTargetHighestLayoutHeadersData
open ActiveTargetHighestPairLayoutGeometry (late early)

variable (s : Shape) (p : Parameters s) (offset rows : ℕ)

theorem late_valid (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before) :
    Valid .late (inputs s p offset rows) := by
  have h := ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.after hfit
  simp only [Valid,inputs,baseWidth]
  unfold ActiveTargetHighestPairLayoutGeometry.sourceHigh at h
  omega

theorem early_valid (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<ActiveTargetHighestPairLayoutGeometry.sourceHigh s p offset) :
    Valid .early (inputs s p offset rows) := by
  have h := ActiveTargetHighestPairLayoutGeometry.source_high_lt s p offset p.before hfit
  simp only [Valid,inputs,sourceHigh,baseWidth]
  unfold ActiveTargetHighestPairLayoutGeometry.sourceHigh at h hsource
  omega

theorem late_values (hfit : offset+p.f*p.q≤p.after) (hbefore : 1≤p.before)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    values .late (inputs s p offset rows)=ActiveTargetHighestPairHeadersData.originalValues
      (late s p offset rows hfit hbefore hH hr hp) := by
  funext i; fin_cases i
  all_goals simp [values,left,gap,suffix,baseWidth,sourceHigh,inputs,late,
    ActiveTargetHighestPairLayoutGeometry.sourceHigh,ActiveTargetHighestPairHeadersData.originalValues]
  omega

theorem early_values (hfit : offset+p.f*p.q≤p.before)
    (hsource : 0<ActiveTargetHighestPairLayoutGeometry.sourceHigh s p offset)
    (hH : 1≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    values .early (inputs s p offset rows)=ActiveTargetHighestPairHeadersData.originalValues
      (early s p offset rows hfit hsource hH hr hp) := by
  funext i; fin_cases i
  all_goals rfl

end IntegerMultBounds.Machine.ActiveTargetHighestLayoutHeadersGeometry
