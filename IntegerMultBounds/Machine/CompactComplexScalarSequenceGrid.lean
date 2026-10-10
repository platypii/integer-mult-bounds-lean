import IntegerMultBounds.Machine.CompactComplexScalarSequenceSemantics
import IntegerMultBounds.Machine.CompactComplexScalarRoleSemantics

/-! Literal scalar-array sequences preserve the dynamic Gaussian grid, with
an explicit numerator bound from the actual listed sparse gates. A genuine contiguous
scalar segment inherits the whole finite network's growth allowance. Intermediate
signed guards still follow from the single stored-field reserve, not callbacks. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarSequenceGrid
noncomputable section
open Networks Networks.GaussianPrecision
open CompactComplexScalarIntegerRows (RowIndex Wire gate)
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarSequenceSemantics (Bound values circuit)
open CompactComplexScalarPolynomialSequence (execute)
open ButterflyStreamData (Coefficient)
attribute [local irreducible] ComplexRank25.program CompactComplexScalarIntegerRows.gates ComplexFramedExecution.rows

private theorem bound_mono {ι : Type*} (d B : ℕ) (gs : List (Circuit.Gate ι ℂ))
    (M N : ℕ) (h : M≤N) : scalarBound d B gs M≤scalarBound d B gs N := by
  rw [scalarBound_linear d B gs M,scalarBound_linear d B gs N]
  exact Nat.mul_le_mul_right _ h

/-- Contiguous actual rows are paid by the complete network budget, including
its true sparse term multiplicities. -/
theorem segment_bound {ι : Type*} (d B M : ℕ)
    (before segment after : List (Circuit.Gate ι ℂ)) :
    scalarBound d B segment M≤scalarBound d B (before++segment++after) M := by
  rw [scalarBound_append,scalarBound_append]
  exact (bound_mono d B segment _ _ (scalarBound_ge d B before M)).trans
    (scalarBound_ge d B after _)

theorem coefficients (ops : List RowIndex) : CircuitCoefficients.All (BoundedGrid 1 52) (circuit ops) := by
  intro g hg t ht
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hg
  obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
  exact CompactComplexScalarIntegerRows.coefficients r t0 ht0

/-- Numerical grid of the exact emitted words after the physical scalar
sequence. Its true denominator rises by exactly the completed row count. -/
theorem sequence_grid {N : ℕ} (ops : List RowIndex)
    (data : Fin wireCount → Fin N → Coefficient) (b p n M : ℕ)
    (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (hb : Bound b p data) (hg : p+ops.length*CompactComplexScalarIntegerRows.guardBits≤b)
    (hgrid : ∀ wire i,BoundedGrid n M (values b n data i wire)) (i : Fin N) (wire : Wire) :
    BoundedGrid (n+ops.length) (scalarBound 1 52 (circuit ops) M)
      (values b (n+ops.length) (execute ops data) i wire) := by
  rw [CompactComplexScalarSequenceSemantics.sequence_values ops data b p n hw hb hg i]
  have h := bounded_run (circuit ops) (values b n data i) n 1 M 52
    (fun wire => hgrid wire i) (coefficients ops) wire
  simpa only [circuit,List.length_map,Nat.mul_one] using h

/-- The dependency Path and original stored width supply all signed guards
for the numerical output grid of the actual scalar sequence. -/
theorem sequence_grid_from_path
    {sh : CompactGadgetReservationShape.Shape} {left k levels frames returned N : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (ops : List RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (p C axes metadataP n : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      ops.length*CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hgrid : ∀ j i,BoundedGrid n
      (CompactComplexScalarPathGuard.budget p C levels frames returned axes)
      (ButterflySigned.complexValue
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth metadataP sh.bits) (data j i).1)
        (ButterflySigned.signedValue (ButterflyGuard.halfWidth metadataP sh.bits) (data j i).2) n))
    (i : Fin N) (wire : Wire) :
    BoundedGrid (n+ops.length)
      (scalarBound 1 52 (circuit ops)
        (CompactComplexScalarPathGuard.budget p C levels frames returned axes))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (execute ops data) i wire) := by
  have hb : Bound (ButterflyGuard.halfWidth metadataP sh.bits)
      (CompactComplexScalarPathGuard.power sh p C axes) data := by
    intro j i
    have hn := ButterflyGuard.represented_bound _ _ n _ (hgrid j i)
    have hg := Int.ofNat_le.mpr (CompactComplexScalarPathGuard.growth_power path p C axes).le
    exact ⟨hn.1.trans hg,hn.2.trans hg⟩
  exact sequence_grid ops data _ (CompactComplexScalarPathGuard.power sh p C axes) n _ hw hb
    (CompactComplexScalarRoleSemantics.stored_reserve sh p C axes metadataP ops.length
      ha hp haxes hroom) (fun wire i => hgrid (CompactComplexScalarIntegerRows.wireIndex wire) i) i wire

/-- The actual segment's dynamic numerator growth is bounded by the same
fixed allowance used in the original dependency Path budget. -/
theorem actual_segment_bound (ops : List RowIndex) (M C : ℕ)
    (before after : List (Circuit.Gate Wire ℂ))
    (hsegment : before++circuit ops++after=RationalScalarGrid.castRows ComplexFramedExecution.rows)
    (hC : CompactFramedScalarGrid.growthConstant≤C) :
    scalarBound 1 52 (circuit ops) M≤M*C := by
  have h := segment_bound 1 52 M before (circuit ops) after
  rw [hsegment,scalarBound_linear 1 52 (RationalScalarGrid.castRows ComplexFramedExecution.rows) M] at h
  unfold CompactFramedScalarGrid.growthConstant at hC
  exact h.trans (Nat.mul_le_mul_left M hC)

/-- An interleaved scalar segment consumes the existing prefix allowance.
The complete node's growth constant is paid once, rather than again for each
segment between recursive calls. -/
theorem sequence_prefix_grid {N : ℕ} (ops : List RowIndex)
    (data : Fin wireCount → Fin N → Coefficient) (b p n M C : ℕ)
    (before after : List (Circuit.Gate Wire ℂ))
    (hsegment : before++circuit ops++after=RationalScalarGrid.castRows ComplexFramedExecution.rows)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hw : ∀ j i,(data j i).1.length=b+1 ∧ (data j i).2.length=b+1)
    (hb : Bound b p data) (hg : p+ops.length*CompactComplexScalarIntegerRows.guardBits≤b)
    (hgrid : ∀ wire i,BoundedGrid n (scalarBound 1 52 before M) (values b n data i wire))
    (i : Fin N) (wire : Wire) :
    BoundedGrid (n+ops.length) (M*C) (values b (n+ops.length) (execute ops data) i wire) := by
  have h := sequence_grid ops data b p n _ hw hb hg hgrid i wire
  have hbound := scalarBound_ge 1 52 after
    (scalarBound 1 52 (before++circuit ops) M)
  rw [←scalarBound_append,hsegment,
    scalarBound_linear 1 52 (RationalScalarGrid.castRows ComplexFramedExecution.rows) M] at hbound
  rw [scalarBound_append] at hbound
  unfold CompactFramedScalarGrid.growthConstant at hC
  exact Networks.GaussianPrecision.bound_mono
    (hbound.trans (Nat.mul_le_mul_left M hC)) h

/-- A real scalar prefix stays within the current node's reserved Path
budget. Ancestor growth and pending butterfly work are separated from the
single scalar growth allowance for this node. -/
theorem sequence_prefix_grid_from_path
    {sh : CompactGadgetReservationShape.Shape} {left k levels frames returned N : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (ops : List RowIndex) (data : Fin wireCount → Fin N → Coefficient)
    (p C axes metadataP n : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : CompactSpectatorInheritedGrid.dependencyCoefficient C+Nat.clog 2 (C+1)+
      ops.length*CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (before after : List (Circuit.Gate Wire ℂ))
    (hsegment : before++circuit ops++after=RationalScalarGrid.castRows ComplexFramedExecution.rows)
    (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hgrid : ∀ wire i,BoundedGrid n
      (scalarBound 1 52 before
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)))
      (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i wire))
    (i : Fin N) (wire : Wire) :
    BoundedGrid (n+ops.length) (CompactComplexScalarPathGuard.budget p C levels frames returned axes)
      (values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
        (execute ops data) i wire) := by
  let M := CompactRecursiveGridBudget.bound p C levels (frames+2*returned+axes)
  have htotal : M*C=CompactComplexScalarPathGuard.budget p C levels frames returned axes :=
    CompactRecursiveGridBudget.scalar_step p C levels (frames+2*returned+axes)
  have hprefix := segment_bound 1 52 M [] before (circuit ops++after)
  simp only [List.nil_append] at hprefix
  have hfull : before++(circuit ops++after)=RationalScalarGrid.castRows ComplexFramedExecution.rows := by
    simpa only [List.append_assoc] using hsegment
  rw [hfull,scalarBound_linear 1 52 (RationalScalarGrid.castRows ComplexFramedExecution.rows) M] at hprefix
  have hconstant := hC
  unfold CompactFramedScalarGrid.growthConstant at hconstant
  have hgrowth : scalarBound 1 52 before M≤M*C := by
    exact hprefix.trans (Nat.mul_le_mul_left M hconstant)
  rw [htotal] at hgrowth
  have hb : Bound (ButterflyGuard.halfWidth metadataP sh.bits)
      (CompactComplexScalarPathGuard.power sh p C axes) data := by
    intro j i
    have h := Networks.GaussianPrecision.bound_mono hgrowth
      (hgrid (CompactComplexScalarIntegerRows.wireIndex.symm j) i)
    simp only [values,Equiv.apply_symm_apply] at h
    have hn := ButterflyGuard.represented_bound _ _ n _ h
    have hg := Int.ofNat_le.mpr (CompactComplexScalarPathGuard.growth_power path p C axes).le
    exact ⟨hn.1.trans hg,hn.2.trans hg⟩
  rw [←htotal]
  exact sequence_prefix_grid ops data _ (CompactComplexScalarPathGuard.power sh p C axes) n M C
    before after hsegment hC hw hb
    (CompactComplexScalarRoleSemantics.stored_reserve sh p C axes metadataP ops.length
      ha hp haxes hroom) hgrid i wire

end
end IntegerMultBounds.Machine.CompactComplexScalarSequenceGrid
