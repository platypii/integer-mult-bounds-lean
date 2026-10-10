import IntegerMultBounds.Machine.CompactComplexScalarSegmentRows

/-! Actual scalar group completion preserves the tighter next-prefix grid,
so subsequent groups consume the remaining single node allowance. The full
Path budget supplies overflow guards but is not substituted for the prefix
postcondition required by the next interleaved event. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarPrefixAdvance
noncomputable section
open Networks Networks.GaussianPrecision
open CompactComplexScalarIntegerRows (RowIndex GroupIndex Wire wireIndex gates guardBits)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarSequenceSemantics (Bound values circuit)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSegmentRows (block)
open ButterflyStreamData (Coefficient)
attribute [local irreducible] ComplexRank25.program CompactComplexScalarIntegerRows.gates
  ComplexFramedExecution.rows

/-- Any current bound below the reserved Path budget supplies signed guards,
while the actual scalar-bound recurrence is retained in the output. -/
theorem sequence_under_path
    {sh : CompactGadgetReservationShape.Shape} {left k levels frames returned N : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (ops : List RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (p C axes metadataP n M : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      ops.length*guardBits≤sh.chunk)
    (hM : M≤CompactComplexScalarPathGuard.budget p C levels frames returned axes)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hgrid : ∀ wire i,BoundedGrid n M
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i wire))
    (i : Fin N) (wire : Wire) :
    BoundedGrid (n+ops.length) (scalarBound 1 52 (circuit ops) M)
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (execute ops data) i wire) := by
  have hb : Bound (ButterflyGuard.halfWidth metadataP sh.bits)
      (CompactComplexScalarPathGuard.power sh p C axes) data := by
    intro j i
    have h := Networks.GaussianPrecision.bound_mono hM (hgrid (wireIndex.symm j) i)
    simp only [values,Equiv.apply_symm_apply] at h
    have hn := ButterflyGuard.represented_bound _ _ n _ h
    have hg := Int.ofNat_le.mpr (CompactComplexScalarPathGuard.growth_power path p C axes).le
    exact ⟨hn.1.trans hg,hn.2.trans hg⟩
  exact CompactComplexScalarSequenceGrid.sequence_grid ops data _
    (CompactComplexScalarPathGuard.power sh p C axes) n M hw hb
    (CompactComplexScalarRoleSemantics.stored_reserve sh p C axes metadataP ops.length
      ha hp haxes hroom) hgrid i wire

/-- The real group finishes on its next original scalar prefix, at the exact
advanced denominator. This stronger postcondition can feed the next group's
input; the node growth constant is charged only once across all groups. -/
theorem group_grid
    {sh : CompactGadgetReservationShape.Shape} {left k levels frames returned N : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (g : GroupIndex) (data : Fin wireCount → Fin N → Coefficient)
    (p C axes metadataP n : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      (gates g).length*guardBits≤sh.chunk)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hgrid : ∀ wire i,BoundedGrid n
      (CompactFramedScalarGrid.bound g.val
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i wire))
    (i : Fin N) (wire : Wire) :
    BoundedGrid (n+(gates g).length)
      (CompactFramedScalarGrid.bound (g.val+1)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+(gates g).length)
        (execute (block g) data) i wire) := by
  let M := CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)
  have hM : CompactFramedScalarGrid.bound g.val M≤
      CompactComplexScalarPathGuard.budget p C levels frames returned axes := by
    have h := CompactFramedScalarGrid.bound_le g.val M C hC
    exact h.trans_eq (CompactRecursiveGridBudget.scalar_step p C levels (frames+2*returned+axes))
  have hroom' : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      (block g).length*guardBits≤sh.chunk := by
    simpa only [CompactComplexScalarSegmentRows.block_length] using hroom
  have h := sequence_under_path path (block g) data p C axes metadataP n
    (CompactFramedScalarGrid.bound g.val M) ha hp haxes hroom' hM hw hgrid i wire
  have hprefix := congrArg (fun gs => scalarBound 1 52 gs M)
    (CompactComplexScalarSegmentRows.prefix_complete g)
  rw [scalarBound_append] at hprefix
  change scalarBound 1 52 (circuit (block g)) (CompactFramedScalarGrid.bound g.val M)=
    CompactFramedScalarGrid.bound (g.val+1) M at hprefix
  rw [hprefix,CompactComplexScalarSegmentRows.block_length] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexScalarPrefixAdvance
