import IntegerMultBounds.Machine.CompactComplexScalarRolePorts
import IntegerMultBounds.Machine.CompactComplexScalarSequenceSemantics
import IntegerMultBounds.Machine.CompactComplexScalarPathGuard

/-! Actual permanent-role scalar execution with its original complex circuit
postcondition. The dependency Path and retained widths derive every intermediate
signed guard; a single finite schedule reserve suffices for the entire block. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarRoleSemantics
noncomputable section
open CompactComplexScalarRowBlock (wireCount)
open CompactComplexScalarIntegerRows (RowIndex guardBits)
open CompactComplexScalarPolynomialSequence (execute)
open CompactComplexScalarSequenceSemantics (Bound values circuit)
open CompactComplexScalarPathGuard (power budget)
open CompactComplexScalarRolePorts (publicTapes Ready readyBank output program)
open CompactRecursiveDependencyBudget (Path)
open CompactSpectatorInheritedGrid (dependencyCoefficient)
open CompactGadgetReservationShape (Shape)
open ButterflyStreamData (Coefficient)
open ButterflySigned (signedValue complexValue)
open Networks.GaussianPrecision (BoundedGrid)
attribute [local irreducible] Networks.ComplexRank25.program CompactComplexScalarIntegerRows.gates

/-- The actual stored fields reserve every row, rather than assuming a fresh
capacity or signed guard at each scalar gate. -/
theorem stored_reserve (sh : Shape) (p C axes metadataP len : ℕ)
    (ha : 0<sh.active) (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+len*guardBits≤sh.chunk) :
    power sh p C axes+len*guardBits≤ButterflyGuard.halfWidth metadataP sh.bits := by
  have hm := Nat.mul_le_mul_right sh.active
    (show dependencyCoefficient C≤sh.chunk from by omega)
  have hdep : dependencyCoefficient C*sh.active≤sh.bits := by unfold Shape.bits; nlinarith
  have hK := Nat.le_mul_of_pos_left sh.chunk ha
  have hbits : sh.chunk≤sh.bits := by unfold Shape.bits; nlinarith
  unfold power ButterflyGuard.halfWidth
  omega

/-- Physical role-stream execution, true live-denominator update and full
complex-circuit semantics follow from the original dependency grid. -/
theorem runs_from_path {sh : Shape} {left k levels frames returned s N : ℕ}
    (path : Path sh.active left k levels frames returned)
    (hs : 7<s) (header : Fin s) (hh : header.val≠7) (ops : List RowIndex)
    (v : Tapes (publicTapes s) 2) (data : Fin wireCount → Fin N → Coefficient)
    (p C axes metadataP n : ℕ) (ha : 0<sh.active)
    (hp : p+2*sh.bits≤metadataP) (haxes : axes≤sh.bits)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+ops.length*guardBits≤sh.chunk)
    (hw : ∀ j i,(data j i).1.length=ButterflyGuard.halfWidth metadataP sh.bits+1 ∧
      (data j i).2.length=ButterflyGuard.halfWidth metadataP sh.bits+1)
    (hgrid : ∀ j i,BoundedGrid n (budget p C levels frames returned axes)
      (complexValue (signedValue (ButterflyGuard.halfWidth metadataP sh.bits) (data j i).1)
        (signedValue (ButterflyGuard.halfWidth metadataP sh.bits) (data j i).2) n))
    (hready : Ready hs header v data n) :
    HoareTime (program hs header hh ops).2
      (fun z => z=readyBank v)
      (fun z => z=readyBank (output hs header v (execute ops data) (n+ops.length)))
      (CompactComplexScalarDenominatorSequence.cost ops N
        (ButterflyGuard.halfWidth metadataP sh.bits+1) n) ∧
    ∀ i,values (ButterflyGuard.halfWidth metadataP sh.bits) (n+ops.length)
      (execute ops data) i=Networks.Circuit.run (circuit ops)
        (values (ButterflyGuard.halfWidth metadataP sh.bits) n data i) := by
  have hb : Bound (ButterflyGuard.halfWidth metadataP sh.bits) (power sh p C axes) data := by
    intro j i
    have hn := ButterflyGuard.represented_bound _ _ n _ (hgrid j i)
    have hg := Int.ofNat_le.mpr (CompactComplexScalarPathGuard.growth_power path p C axes).le
    exact ⟨hn.1.trans hg,hn.2.trans hg⟩
  exact ⟨CompactComplexScalarRolePorts.runs hs header hh ops v data _ n hw hready,
    fun i => CompactComplexScalarSequenceSemantics.sequence_values ops data _
      (power sh p C axes) n hw hb (stored_reserve sh p C axes metadataP ops.length ha hp haxes hroom) i⟩

/-- The original chunk schedule eventually pays the entire fixed scalar block. -/
theorem eventually_sequence_room (C : ℕ) (ops : List RowIndex) : ∀ᶠ n : ℕ in Filter.atTop,
    dependencyCoefficient C+Nat.clog 2 (C+1)+ops.length*guardBits≤Sizes.K n :=
  CompactComplexScalarPathGuard.eventually_chunk_room _

end
end IntegerMultBounds.Machine.CompactComplexScalarRoleSemantics
