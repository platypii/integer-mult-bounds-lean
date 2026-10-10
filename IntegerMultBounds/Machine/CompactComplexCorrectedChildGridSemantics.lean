import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetPrefix
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedSemantics

/-! Corrected child tensor semantics propagates the selected-stream grid and
actual parent spectator promotion. Recursive tensor correctness remains an
explicit induction hypothesis; no uncorrected network execution is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedChildGridSemantics
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid (Width Grid decoded half)
open CompactComplexNonleafChildAddress (roles inputIndex outputWire outputAddress childVisit)
open CompactComplexNonleafEventProgress (aligned)
open Networks
open Networks.GaussianPrecision
variable {left k c : ℕ}

private theorem bounded_star {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid n M (star z) := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  refine ⟨a,-b,?_,ha,by simpa only [abs_neg] using hb⟩
  have hc := congrArg star he
  simpa using hc

/-- The completed call applies the actual corrected tensor or its inverse. -/
def tensor (call : ComplexRecursiveCallSchema.Call)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    (wire : ComplexFramedExecution.Wire) (address : BinaryColumns.Address (25^3) (arity^k)) : ℂ :=
  if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm (stored wire) address
  else ComplexEndpoints.fullFrame (arity^k) (stored wire) address

/-- Both actual directions have the same true return denominator and bound. -/
theorem tensor_grid (call : ComplexRecursiveCallSchema.Call) (n k M : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    (hg : ∀ wire address,BoundedGrid n M (stored wire address))
    (wire : ComplexFramedExecution.Wire) (address : BinaryColumns.Address (25^3) (arity^k)) :
    BoundedGrid (n+2*arity^(k+1)) (M*4^(2*arity^(k+1)))
      (tensor call stored wire address) := by
  have hf (f : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
      (h : ∀ wire address,BoundedGrid n M (f wire address)) :=
    CompactComplexSourceReadyNonleafOrientedSemantics.corrected_grid n k M f h wire address
  unfold tensor
  split_ifs
  · have h := hf (fun wire address => star (stored wire address))
      (fun wire address => bounded_star (hg wire address))
    rw [ComplexEndpoints.corrected_network_run] at h
    have hs := bounded_star h
    rw [CompactComplexSourceReadyNonleafOrientedSemantics.inverse_full_tensor] at hs
    exact hs
  · have h := hf stored hg
    rw [ComplexEndpoints.corrected_network_run] at h
    exact h

/-- Actual corrected child semantics on each original spectator slice derives
its grid from the parent's input grid, without an uncorrected-network premise. -/
theorem corrected_selected_grid (sh : Shape) (rows ell q n M : ℕ) (hd : roles∣rows)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (call : ComplexRecursiveCallSchema.Call) (before child : Array sh rows ell)
    (hg : Grid sh rows ell q n M before)
    (hsem : ∀ i,decoded sh rows ell q (n+2*arity^(k+1)) child i=
      tensor call (fun wire address => decoded sh rows ell q n before
        (inputIndex sh rows ell hd rho visit i wire address))
        (outputWire sh rows ell hd i) (outputAddress sh rows ell hd rho visit i)) :
    Grid sh rows ell q (n+2*arity^(k+1)) (M*4^(2*arity^(k+1))) child := by
  intro i
  rw [hsem]
  exact tensor_grid call n k M _ (fun wire address => hg _) _ _

/-- The real corrected return and literal spectator shifts yield one common
parent denominator, retaining every untouched role's decoded value. -/
theorem corrected_shared_grid (sh : Shape) (rows ell q n M : ℕ) (selected : Fin c)
    (before : Fin c → Array sh rows ell) (child : Array sh rows ell)
    (hd : roles∣rows) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+1))
    (call : ComplexRecursiveCallSchema.Call)
    (hw : ∀ role,Width sh rows ell q (before role))
    (hg : ∀ role,Grid sh rows ell q n M (before role))
    (hsem : ∀ i,decoded sh rows ell q (n+2*arity^(k+1)) child i=
      tensor call (fun wire address => decoded sh rows ell q n (before selected)
        (inputIndex sh rows ell hd rho visit i wire address))
        (outputWire sh rows ell hd i) (outputAddress sh rows ell hd rho visit i))
    (hcapacity : 2*arity^(k+1)≤half sh q+1)
    (hguard : M*2^(2*arity^(k+1))<2^(half sh q)) :
    (∀ role,Grid sh rows ell q (n+2*arity^(k+1)) (M*4^(2*arity^(k+1)))
      (aligned sh rows ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh rows ell q (n+2*arity^(k+1))
      (aligned sh rows ell k selected before child role)=decoded sh rows ell q n (before role)) := by
  have hc := corrected_selected_grid sh rows ell q n M hd rho visit call (before selected) child
    (hg selected) hsem
  exact CompactComplexChildGridAlignment.shared_grid sh rows ell q n M (2*arity^(k+1)) selected before
    (aligned sh rows ell k selected before child) hg (by simpa only [aligned,ite_true] using hc)
    (fun role hr i => by
      simp only [aligned,ite_eq_right hr]
      exact CompactComplexChildGridPromoted.promotes sh rows ell q n M _ (before role)
        (hw role) (hg role) hcapacity hguard i)

/-- The original prefix budget pays the true corrected child tensor and
promotion, advancing its returned count by the actual child interval size. -/
theorem corrected_prefix_grid (sh : Shape) (rows ell q n k g baselineP C levels frames returned axes : ℕ)
    (selected : Fin c) (before : Fin c → Array sh rows ell) (child : Array sh rows ell)
    (hd : roles∣rows) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call)
    (hw : ∀ role,Width sh rows ell q (before role))
    (hg : ∀ role,Grid sh rows ell q n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
        (frames+2*returned+axes))) (before role))
    (hsem : ∀ i,decoded sh rows ell q (n+2*arity^(k+1)) child i=
      tensor call (fun wire address => decoded sh rows ell q n (before selected)
        (inputIndex sh rows ell hd rho (childVisit visit call) i wire address))
        (outputWire sh rows ell hd i) (outputAddress sh rows ell hd rho (childVisit visit call) i))
    (hcapacity : 2*arity^(k+1)≤half sh q+1)
    (hguard : CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
      (frames+2*returned+axes))*2^(2*arity^(k+1))<2^(half sh q)) :
    (∀ role,Grid sh rows ell q (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
        (frames+2*(returned+arity^(k+1))+axes))) (aligned sh rows ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh rows ell q (n+2*arity^(k+1))
      (aligned sh rows ell k selected before child role)=decoded sh rows ell q n (before role)) := by
  have hs := corrected_shared_grid sh rows ell q n _ selected before child hd rho (childVisit visit call)
    call hw hg hsem hcapacity hguard
  refine ⟨?_,hs.2⟩
  intro role
  rw [←CompactComplexNonleafEventProgress.prefix_bound g baselineP C levels frames returned axes (arity^(k+1))]
  exact hs.1 role

/-- Genuine original Path and retained-width reserve discharge every
spectator promotion guard for the corrected child return. -/
theorem corrected_prefix_grid_from_path (sh : Shape)
    (rows ell metadataP n k g baselineP C levels frames returned axes : ℕ)
    (selected : Fin c) (before : Fin c → Array sh rows ell) (child : Array sh rows ell)
    (hd : roles∣rows) (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (call : ComplexRecursiveCallSchema.Call)
    {pathLeft pathDimension : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active pathLeft pathDimension levels frames returned)
    (ha : 0<sh.active) (hp : baselineP+2*sh.bits≤metadataP)
    (haxes : axes+2*arity^(k+1)≤sh.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hw : ∀ role,Width sh rows ell (metadataP-2*sh.bits) (before role))
    (hg : ∀ role,Grid sh rows ell (metadataP-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
        (frames+2*returned+axes))) (before role))
    (hsem : ∀ i,decoded sh rows ell (metadataP-2*sh.bits) (n+2*arity^(k+1)) child i=
      tensor call (fun wire address => decoded sh rows ell (metadataP-2*sh.bits) n (before selected)
        (inputIndex sh rows ell hd rho (childVisit visit call) i wire address))
        (outputWire sh rows ell hd i) (outputAddress sh rows ell hd rho (childVisit visit call) i)) :
    (∀ role,Grid sh rows ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
        (frames+2*(returned+arity^(k+1))+axes))) (aligned sh rows ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh rows ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (aligned sh rows ell k selected before child role)=
        decoded sh rows ell (metadataP-2*sh.bits) n (before role)) := by
  have hguard := CompactComplexNonleafEventProgress.promotion_from_path path
    g baselineP C axes k metadataP ha hp haxes hC hroom
  exact corrected_prefix_grid sh rows ell (metadataP-2*sh.bits) n k g baselineP C levels frames returned axes
    selected before child hd rho visit call hw hg hsem hguard.1 hguard.2

end
end IntegerMultBounds.Machine.CompactComplexCorrectedChildGridSemantics
