import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalSemantics
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedEndpoint
import IntegerMultBounds.Networks.ComplexInverseExecution

/-! Genuine nonleaf contraction and saved-call post-orientation have exact
Gaussian semantics. Negation safety is derived from the completed network,
original Path and retained signed reserve, including endpoint corrections. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedSemantics
noncomputable section
open Networks
open GaussianPrecision (BoundedGrid)
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexControllerExactReturn (contracted)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactSpectatorInheritedGrid (decoded Grid)
open CompactRecursiveDependencyBudget (Path)

private theorem bounded_star {n M : ℕ} {z : ℂ} (hz : BoundedGrid n M z) :
    BoundedGrid n M (star z) := by
  obtain ⟨a,b,he,ha,hb⟩ := hz
  refine ⟨a,-b,?_,ha,by simpa only [abs_neg] using hb⟩
  have hc := congrArg star he
  simpa using hc

/-- Real nonleaf volume and the existing chunk reserve pay twice-volume
endpoint growth; this is derived from the actual dependency visit. -/
theorem endpoint_work {sh : Shape} {left k levels frames returned : ℕ}
    (path : Path sh.active left (k+1) levels frames returned) (C : ℕ)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk) :
    2*arity^(k+1)≤sh.bits := by
  have hfit := path.visit.fits
  have htwo : 2≤sh.chunk := by
    unfold CompactSpectatorInheritedGrid.dependencyCoefficient CompactRecursiveDependencyBudget.volumeCoefficient at hchunk
    omega
  have h := Nat.mul_le_mul hfit htwo
  unfold Shape.bits
  nlinarith

/-- Conjugation is safe on the genuine completed-network endpoint, whose
numerator bound follows from original Path/Grid growth and the full network.
No separately assumed conjugatable-output predicate is needed. -/
theorem post_grid {sh : Shape} {left k levels frames returned rows ell q : ℕ}
    (call : ComplexRecursiveCallSchema.Call)
    (path : Path sh.active left (k+1) levels frames returned)
    (baseline C target : ℕ) (hb : baseline≤q)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : Grid sh rows ell q target
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(2*arity^(k+1))) f) :
    Grid sh rows ell q target
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(2*arity^(k+1))) (oriented call f) ∧
    CompactSpectatorInheritedGrid.Width sh rows ell q (oriented call f) ∧
    decoded sh rows ell q target (oriented call f)=
      fun i => if call.inverse then star (decoded sh rows ell q target f i) else decoded sh rows ell q target f i := by
  have hguard := CompactSpectatorInheritedGrid.guard_from_path sh q path baseline C (2*arity^(k+1))
    hb hchunk (endpoint_work path C hchunk)
  have hlt : CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(2*arity^(k+1))<
      2^(CompactSpectatorInheritedGrid.half sh q) := by omega
  have hlt' : ((CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(2*arity^(k+1))):ℤ)<
      (2^(CompactSpectatorInheritedGrid.half sh q):ℕ) := by exact_mod_cast hlt
  have he : decoded sh rows ell q target (NativePolynomialConjugationData.array f)=
      fun i => star (decoded sh rows ell q target f i) := by
    funext i
    have hbound := ButterflyGuard.represented_bound _ _ target _ (hg i)
    apply NativePolynomialConjugationData.decoded
    · simpa only [ButterflyGuard.width,ButterflyIndependentGuardSemantics.half_eq] using (hw i).2
    · exact hbound.2.trans_lt hlt'
  unfold oriented
  split_ifs
  · refine ⟨?_,?_,he⟩
    · intro i
      rw [congrFun he i]
      exact bounded_star (hg i)
    · intro i
      simpa only [NativePolynomialConjugationData.array,NativePolynomialConjugationData.coefficient,
        NativePolynomialConjugationData.negative_length] using hw i
  · exact ⟨hg,hw,rfl⟩

theorem post_completed (sh : Shape) (rows ell p current n k : ℕ)
    (hP : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (wires : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)) → ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)) → BinaryColumns.Address (25^3) (arity^k))
    (original : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    {left levels frames returned : ℕ}
    (path : Path sh.active left (k+1) levels frames returned)
    (baseline C R base usedRows : ℕ) (hb : baseline≤p-2*sh.bits)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hg : ∀ wire address,BoundedGrid n
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)) (original wire address))
    (hcompleted : ∀ i,decoded sh rows ell (p-2*sh.bits) current f i=
      FramedCircuit.run (ComplexFramedExecution.network (arity^k)) original (wires i) (addresses i))
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hbase : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    (call : ComplexRecursiveCallSchema.Call) :
    let target := CompactComplexDenominatorPolicy.networkTarget n k
    let out := contracted (current-target) f
    Grid sh rows ell (p-2*sh.bits) target
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(2*arity^(k+1))) (oriented call out) ∧
    (∀ i,((oriented call out) i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      ((oriented call out) i).2.length=CompactNativeRoleHeaders.recordWidth sh p) ∧
    decoded sh rows ell (p-2*sh.bits) target (oriented call out)=
      fun i => if call.inverse then star (FramedCircuit.run (ComplexFramedExecution.network (arity^k)) original
        (wires i) (addresses i)) else FramedCircuit.run (ComplexFramedExecution.network (arity^k)) original
        (wires i) (addresses i) := by
  let M := CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)
  let target := CompactComplexDenominatorPolicy.networkTarget n k
  let out := contracted (current-target) f
  have he := CompactComplexSourceReadyNonleafFinalSemantics.completed sh rows ell p current n k M hP f hw
    wires addresses original hg hcompleted hledger path R base usedRows hbase hu hroom hlive
  change ∀ i,decoded sh rows ell (p-2*sh.bits) target out i=
    FramedCircuit.run (ComplexFramedExecution.network (arity^k)) original (wires i) (addresses i) at he
  have hout : ∀ i,(out i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (out i).2.length=CompactNativeRoleHeaders.recordWidth sh p :=
    CompactComplexSourceReadyNonleafFinalGeometry.contracted_width _ f hw
  have hstored := CompactSpectatorInheritedGrid.width_from_retained_role sh rows ell p hP out hout
  have hgrid : Grid sh rows ell (p-2*sh.bits) target (M*4^(2*arity^(k+1))) out := by
    intro i
    rw [he i]
    exact CompactComplexDenominatorPolicy.network_grid n k M original hg (wires i) (addresses i)
  obtain ⟨hgo,hwo,heo⟩ := post_grid call path baseline C target hb hchunk out hstored hgrid
  refine ⟨hgo,?_,?_⟩
  · unfold oriented
    split_ifs
    · intro i
      simpa only [NativePolynomialConjugationData.array,NativePolynomialConjugationData.coefficient,
        NativePolynomialConjugationData.negative_length] using hout i
    · exact hout
  · rw [heo]
    funext i
    rw [he i]


/-- Corrected tensor output has the genuine network return denominator and
fresh numerator bound, including the actual source/sink corrections. -/
theorem corrected_grid (n k M : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    (hg : ∀ wire address,BoundedGrid n M (stored wire address))
    (wire : ComplexFramedExecution.Wire) (address : BinaryColumns.Address (25^3) (arity^k)) :
    BoundedGrid (CompactComplexDenominatorPolicy.networkTarget n k) (M*4^(2*arity^(k+1)))
      (ComplexEndpoints.correctOutput (arity^k)
        (FramedCircuit.run (ComplexFramedExecution.network (arity^k))
          (ComplexEndpoints.correctInput (arity^k) stored)) wire address) := by
  rw [ComplexEndpoints.corrected_network_run]
  have h := GaussianPrecision.bounded_tensor_phase_frame BinaryPhase.weightPhase (stored wire) (hg wire) address
  have hN : arity^k*(25^3)=arity^(k+1) := by rw [pow_succ]; rfl
  change BoundedGrid (n+arity^k*(25^3)) (M*4^(arity^k*(25^3)))
    (ComplexEndpoints.fullFrame (arity^k) (stored wire) address) at h
  rw [hN] at h
  have hraise := GaussianPrecision.bounded_raise h (arity^(k+1))
  have hpow : 2^(arity^(k+1))≤4^(arity^(k+1)) := Nat.pow_le_pow_left (by decide : 2≤4) _
  have hm : M*4^(arity^(k+1))*2^(arity^(k+1))≤M*4^(2*arity^(k+1)) := by
    have hh := Nat.mul_le_mul_left (M*4^(arity^(k+1))) hpow
    rw [show 2*arity^(k+1)=arity^(k+1)+arity^(k+1) by omega,Nat.pow_add 4 (arity^(k+1)) (arity^(k+1))]
    simpa only [Nat.mul_assoc] using hh
  exact GaussianPrecision.bound_mono hm (by simpa only [CompactComplexDenominatorPolicy.networkTarget,two_mul,Nat.add_assoc] using hraise)

/-- The true inverse identity is the original corrected inverse-network
theorem, with both corrected endpoint maps retained. -/
theorem inverse_full_tensor (k : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    (wire : ComplexFramedExecution.Wire) (address : BinaryColumns.Address (25^3) (arity^k)) :
    star (ComplexEndpoints.fullFrame (arity^k) (fun x => star (stored wire x)) address)=
      (ComplexEndpoints.fullFrame (arity^k)).symm (stored wire) address := by
  have h := ComplexInverseExecution.corrected_inverse_network (arity^k) stored
  rw [ComplexFramedConjugation.corrected_network_run] at h
  exact congrFun (congrFun h wire) address

/-- Original full-bank input is oriented once before every corrected forward
node. All scratch wires are part of the same actual bank. -/
def oriented_bank (call : ComplexRecursiveCallSchema.Call)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k)) :=
  if call.inverse then ComplexFramedConjugation.bankConjugate stored else stored

theorem corrected_post_completed (sh : Shape) (rows ell p current n k : ℕ)
    (hP : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (wires : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)) → ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size rows sh.bits (2^ell)) → BinaryColumns.Address (25^3) (arity^k))
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) (arity^k))
    (call : ComplexRecursiveCallSchema.Call)
    {left levels frames returned : ℕ}
    (path : Path sh.active left (k+1) levels frames returned)
    (baseline C R base usedRows : ℕ) (hb : baseline≤p-2*sh.bits)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hg : ∀ wire address,BoundedGrid n
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)) (stored wire address))
    (hcompleted : ∀ i,decoded sh rows ell (p-2*sh.bits) current f i=
      ComplexEndpoints.correctOutput (arity^k)
        (FramedCircuit.run (ComplexFramedExecution.network (arity^k))
          (ComplexEndpoints.correctInput (arity^k) (oriented_bank call stored))) (wires i) (addresses i))
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hbase : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let target := CompactComplexDenominatorPolicy.networkTarget n k
    let out := oriented call (contracted (current-target) f)
    Grid sh rows ell (p-2*sh.bits) target
      (CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)*4^(2*arity^(k+1))) out ∧
    (∀ i,(out i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (out i).2.length=CompactNativeRoleHeaders.recordWidth sh p) ∧
    decoded sh rows ell (p-2*sh.bits) target out=
      fun i => if call.inverse then (ComplexEndpoints.fullFrame (arity^k)).symm (stored (wires i)) (addresses i)
        else ComplexEndpoints.fullFrame (arity^k) (stored (wires i)) (addresses i) := by
  let M := CompactRecursiveGridBudget.bound baseline C levels (frames+2*returned)
  let target := CompactComplexDenominatorPolicy.networkTarget n k
  let result := contracted (current-target) f
  have hin : ∀ wire address,BoundedGrid n M (oriented_bank call stored wire address) := by
    unfold oriented_bank
    split_ifs
    · intro wire address
      exact bounded_star (hg wire address)
    · exact hg
  have hgrid : ∀ i,BoundedGrid target (M*4^(2*arity^(k+1)))
      (decoded sh rows ell (p-2*sh.bits) current f i) := by
    intro i
    rw [hcompleted]
    exact corrected_grid n k M _ hin (wires i) (addresses i)
  have hcapacity := CompactComplexControllerExactReturnBudget.current_capacity path R base (p-2*sh.bits)
    usedRows current hbase hu hroom hlive
  have hgap : current-target≤CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by omega
  have hwidth : ∀ i,(f i).1.length=CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 ∧
      (f i).2.length=CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by
    have hp : CompactNativeRoleHeaders.recordWidth sh p=CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by
      unfold CompactNativeRoleHeaders.recordWidth CompactSpectatorInheritedGrid.half ButterflyGuard.width ButterflyGuard.halfWidth
      omega
    simpa only [hp] using hw
  have hexact := CompactComplexControllerExactReturn.contracted_exact f
    (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)) current target _
    (CompactComplexDenominatorPolicy.network_target_le_current n k current hledger) hgap hwidth hgrid
  have he : decoded sh rows ell (p-2*sh.bits) target result=
      decoded sh rows ell (p-2*sh.bits) current f := by funext i; exact hexact.2 i
  have hout := CompactComplexSourceReadyNonleafFinalGeometry.contracted_width (current-target) f hw
  have hstored := CompactSpectatorInheritedGrid.width_from_retained_role sh rows ell p hP result hout
  have hreturned : Grid sh rows ell (p-2*sh.bits) target (M*4^(2*arity^(k+1))) result := by
    intro i
    rw [he,hcompleted]
    exact corrected_grid n k M _ hin (wires i) (addresses i)
  obtain ⟨hgo,hwo,heo⟩ := post_grid call path baseline C target hb hchunk result hstored hreturned
  refine ⟨hgo,?_,?_⟩
  · unfold oriented
    split_ifs
    · intro i
      simpa only [NativePolynomialConjugationData.array,NativePolynomialConjugationData.coefficient,
        NativePolynomialConjugationData.negative_length] using hout i
    · exact hout
  · rw [heo,he]
    funext i
    rw [hcompleted,ComplexEndpoints.corrected_network_run]
    unfold oriented_bank
    split_ifs
    · exact inverse_full_tensor k stored (wires i) (addresses i)
    · rfl

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedSemantics
