import IntegerMultBounds.Machine.CompactComplexStoppedEventProgress
import IntegerMultBounds.Machine.CompactComplexDenominatorPolicy

/-! A normalized nonleaf child advances the denominator by twice its volume,
but advances the parent's returned-child ledger by its volume only. Exact
network semantics supply the selected grid; literal spectator promotion then
preserves the original scalar prefix without charging another scalar-growth
constant. Physical recursive execution and its address maps remain obligations. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafEventProgress
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexRecursiveGeometry (arity)
open Networks Networks.GaussianPrecision

abbrev Index (s : Shape) (rows ell : ℕ) := Fin (ButterflySpectatorGeometry.Size rows s.bits (2^ell))
abbrev Address (k : ℕ) := BinaryColumns.Address (25^3) (arity^k)

def aligned {ι : Type*} [DecidableEq ι] (s : Shape) (rows ell k : ℕ)
    (selected : ι) (before : ι → Array s rows ell) (child : Array s rows ell) :=
  fun role => if role=selected then child
    else CompactComplexChildGridPromoted.promote s rows ell (2*arity^(k+1)) (before role)

theorem prefix_bound (g p C levels frames returned axes volume : ℕ) :
    CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*4^(2*volume)=
    CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+volume)+axes)) := by
  unfold CompactFramedScalarGrid.bound CompactRecursiveGridBudget.bound
  rw [show frames+2*(returned+volume)+axes=(frames+2*returned+axes)+2*volume by omega,pow_add]
  conv_lhs => rw [GaussianPrecision.scalarBound_linear]
  conv_rhs => rw [GaussianPrecision.scalarBound_linear]
  ring

/-- The input to the child's actual network is reconstructed from the selected
parent stream. No independent child grid certificate or coarse scalar bound
is supplied. The completed execution equality is the recursive hypothesis. -/
theorem selected_grid (s : Shape) (rows ell q n M k : ℕ)
    (before child : Array s rows ell)
    (inputIndex : ComplexFramedExecution.Wire → Address k → Index s rows ell)
    (outputWire : Index s rows ell → ComplexFramedExecution.Wire)
    (outputAddress : Index s rows ell → Address k)
    (hg : Grid s rows ell q n M before)
    (hcompleted : ∀ i,decoded s rows ell q (n+2*arity^(k+1)) child i=
      FramedCircuit.run (ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded s rows ell q n before (inputIndex wire address))
        (outputWire i) (outputAddress i)) :
    Grid s rows ell q (n+2*arity^(k+1)) (M*4^(2*arity^(k+1))) child := by
  intro i
  rw [hcompleted]
  exact CompactComplexDenominatorPolicy.network_grid n k M _
    (fun wire address => hg (inputIndex wire address)) (outputWire i) (outputAddress i)

/-- The genuine dependency Path and retained reserve derive both promotion
capacity and signed guard. Runtime working widths do not supply this budget. -/
theorem promotion_from_path {s : Shape} {left dimension levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path s.active left dimension levels frames returned)
    (g p C axes k metadataP : ℕ) (ha : 0<s.active)
    (hp : p+2*s.bits≤metadataP) (haxes : axes+2*arity^(k+1)≤s.bits)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+
      CompactComplexScalarIntegerRows.guardBits≤s.chunk) :
    2*arity^(k+1)≤half s (metadataP-2*s.bits)+1 ∧
    CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*
        2^(2*arity^(k+1))<2^(half s (metadataP-2*s.bits)) := by
  have hg := CompactComplexStoppedEventProgress.prefix_guard_from_path path g p C axes
    (2*arity^(k+1)) metadataP ha hp haxes hC hroom
  refine ⟨?_,?_⟩
  · unfold half ButterflyGuard.halfWidth
    omega
  · have hpow : 2^(2*arity^(k+1))≤4^(2*arity^(k+1)) :=
      Nat.pow_le_pow_left (by decide) _
    have hmul := Nat.mul_le_mul_left
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))) hpow
    exact (hmul.trans (by omega)).trans_lt hg

/-- Parent scalar-prefix and dependency levels remain unchanged. The returned
counter pays two volume contributions, including the normalized child's
semantic numerator growth and the genuine denominator promotion. -/
theorem prefix_grid {ι : Type*} [DecidableEq ι]
    (s : Shape) (rows ell q n k g p C levels frames returned axes : ℕ)
    (selected : ι) (before : ι → Array s rows ell) (child : Array s rows ell)
    (inputIndex : ComplexFramedExecution.Wire → Address k → Index s rows ell)
    (outputWire : Index s rows ell → ComplexFramedExecution.Wire)
    (outputAddress : Index s rows ell → Address k)
    (hw : ∀ role,Width s rows ell q (before role))
    (hg : ∀ role,Grid s rows ell q n
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))) (before role))
    (hcompleted : ∀ i,decoded s rows ell q (n+2*arity^(k+1)) child i=
      FramedCircuit.run (ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded s rows ell q n (before selected) (inputIndex wire address))
        (outputWire i) (outputAddress i))
    (hcapacity : 2*arity^(k+1)≤half s q+1)
    (hguard : CompactFramedScalarGrid.bound g
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes))*
        2^(2*arity^(k+1))<2^(half s q)) :
    (∀ role,Grid s rows ell q (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+arity^(k+1))+axes)))
      (aligned s rows ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded s rows ell q (n+2*arity^(k+1))
      (aligned s rows ell k selected before child role)=decoded s rows ell q n (before role)) := by
  have hc := selected_grid s rows ell q n _ k (before selected) child inputIndex outputWire outputAddress
    (hg selected) hcompleted
  have hs := CompactComplexChildGridAlignment.shared_grid s rows ell q n _ (2*arity^(k+1)) selected
    before (aligned s rows ell k selected before child) hg (by simpa only [aligned,ite_true] using hc)
    (fun role hr i => by
      simp only [aligned,ite_eq_right hr]
      exact CompactComplexChildGridPromoted.promotes s rows ell q n _ _ (before role)
        (hw role) (hg role) hcapacity hguard i)
  refine ⟨?_,hs.2⟩
  intro role
  rw [←prefix_bound g p C levels frames returned axes (arity^(k+1))]
  exact hs.1 role

end
end IntegerMultBounds.Machine.CompactComplexNonleafEventProgress
