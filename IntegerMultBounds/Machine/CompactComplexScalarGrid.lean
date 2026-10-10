import IntegerMultBounds.Networks.GaussianBoundedMotif
import IntegerMultBounds.Networks.CircuitCoefficients
import IntegerMultBounds.Networks.ComplexRank25
import IntegerMultBounds.Machine.ButterflyGuard

/-! Every prefix of the actual complex25 scalar cancellation network has an
explicit precision and numerator bound on all actual roles. Initial bounded
numerators are derived from normalized stored values, not a grid callback. -/
namespace IntegerMultBounds.Machine.CompactComplexScalarGrid
noncomputable section
open Networks Networks.GaussianPrecision
open ComplexRank25
open ButterflySigned
abbrev Role := Wires.ComplexRole 25

def scalarProgram : Circuit.Program Role ℂ :=
  GlobalCircuit.program triples pairs (Equiv.refl (Fin 26))
    (fun i j => (Circuit.complexCopy (GlobalCircuit.complexLocalPairs triples pairs) i j : ℂ))
    (fun i j => (gather i j : ℂ)) (fun i j => (inject i j : ℂ)) (fun i j => (scatter i j : ℂ))

theorem coefficients : CircuitCoefficients.All (BoundedGrid 1 52) scalarProgram := by
  apply CircuitCoefficients.global _ (fun _ h => bounded_neg h)
  · intro i j
    exact bound_mono (by norm_num : 1*2^1≤52)
      (bounded_raise (bounded_complexCopy (GlobalCircuit.complexLocalPairs triples pairs) i j) 1)
  · intro i j
    exact bound_mono (by norm_num : 1*2^1≤52)
      (bounded_raise (bounded_complexGather (fun i => (triples i).val) i j) 1)
  · intro i j
    exact bound_mono (by norm_num : 25+1≤52)
      (bounded_complexInject (GlobalCircuit.complexLocalPairs triples pairs) i j)
  · intro i j
    exact bound_mono (by norm_num : 1≤52)
      (bounded_complexScatter (fun i => (triples i).val) i j)

def numeratorBound (p k : ℕ) := scalarBound 1 52 (scalarProgram.take k) (2^p)

/-- Fixed finite scalar network growth, independent of input size and row count. -/
@[irreducible] def growthConstant := scalarBound 1 52 scalarProgram 1

@[irreducible] def guardBits := Nat.clog 2 (growthConstant+1)

theorem numeratorBound_le (p k : ℕ) : numeratorBound p k≤2^p*growthConstant := by
  calc
    _ ≤ scalarBound 1 52 scalarProgram (2^p) := scalarBound_prefix_le 1 52 scalarProgram (2^p) k
    _ = _ := by
      unfold growthConstant
      exact scalarBound_linear 1 52 scalarProgram (2^p)


theorem guard_helper (p C M b : ℕ) (hM : M≤2^p*C) (hC : C+1≤2^b) : M<2^(p+b) := by
  have hp : 0<2^p := by positivity
  have hs := Nat.mul_lt_mul_of_pos_left (by omega : C<2^b) hp
  rw [←pow_add] at hs
  exact hM.trans_lt hs

theorem numerator_guard (p k C : ℕ) (hC : growthConstant≤C) :
    numeratorBound p k<2^(p+Nat.clog 2 (C+1)) := by
  apply guard_helper p C _ (Nat.clog 2 (C+1))
  · exact (numeratorBound_le p k).trans (Nat.mul_le_mul_left _ hC)
  · exact Nat.le_pow_clog (by decide : 1<2) (C+1)

theorem scalar_prefix (r : Role → ℂ) (p k : ℕ) (hr : ∀ i,BoundedGrid p (2^p) (r i)) :
    ∀ i,BoundedGrid (p+(scalarProgram.take k).length) (numeratorBound p k)
      (Circuit.run (scalarProgram.take k) r i) := by
  simpa only [Nat.mul_one,numeratorBound] using bounded_prefix scalarProgram r p 1 (2^p) 52 k hr coefficients

/-- A scalar-prefix update multiplies the current budget by one fixed network
constant, regardless of the inherited recursive precision or magnitude. -/
theorem inherited_prefix (r : Role → ℂ) (n M k C : ℕ)
    (hr : ∀ i,BoundedGrid n M (r i)) (hC : growthConstant≤C) :
    ∀ i,BoundedGrid (n+(scalarProgram.take k).length) (M*C)
      (Circuit.run (scalarProgram.take k) r i) := by
  have hb : scalarBound 1 52 (scalarProgram.take k) M≤M*C := by
    calc
      _ ≤ scalarBound 1 52 scalarProgram M := scalarBound_prefix_le 1 52 scalarProgram M k
      _ = M*growthConstant := by
        unfold growthConstant
        exact scalarBound_linear 1 52 scalarProgram M
      _ ≤ M*C := Nat.mul_le_mul_left M hC
  intro i
  apply bound_mono hb
  simpa only [Nat.mul_one] using bounded_prefix scalarProgram r n 1 M 52 k hr coefficients i

theorem normalized_grid (a b : ℤ) (p : ℕ) (hn : ‖complexValue a b p‖≤1) :
    BoundedGrid p (2^p) (complexValue a b p) := by
  obtain ⟨ha,hb⟩ := ButterflyGuard.normalized_bound a b p hn
  refine ⟨a,b,?_,ha,hb⟩
  exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2:ℂ)≠0))

/-- Literal normalized initial roles, including genuine zero scratch, derive
all precision and numerator budgets at every actual scalar-prefix boundary. -/
theorem normalized_prefix (a b : Role → ℤ) (p k : ℕ)
    (hn : ∀ i,‖complexValue (a i) (b i) p‖≤1) :
    ∀ i,BoundedGrid (p+(scalarProgram.take k).length) (numeratorBound p k)
      (Circuit.run (scalarProgram.take k) (fun i => complexValue (a i) (b i) p) i) :=
  scalar_prefix _ p k (fun i => normalized_grid _ _ p (hn i))

end
end IntegerMultBounds.Machine.CompactComplexScalarGrid
