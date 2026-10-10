import IntegerMultBounds.Networks.ComplexEndpoints
import IntegerMultBounds.Networks.BinaryWalshComplexConjugation

/-! Conjugating the actual framed network retains every original rational
gate and changes its frames. These are exact array semantics, not tape runs. -/
namespace IntegerMultBounds.Networks.ComplexFramedConjugation
noncomputable section
open FramedCircuit BinaryWalshComplexConjugation

def conjugation (Ω : Type*) : (Ω → ℂ) ≃ₗ[ℚ] (Ω → ℂ) where
  toFun f x := star (f x)
  invFun f x := star (f x)
  left_inv f := by funext x; exact star_star _
  right_inv f := by funext x; exact star_star _
  map_add' f g := by funext x; exact star_add _ _
  map_smul' r f := by
    funext x
    simp [Rat.smul_def,star_mul,mul_comm]

@[simp] theorem conjugation_apply {Ω : Type*} (f : Ω → ℂ) (x : Ω) :
    conjugation Ω f x=star (f x) := rfl

@[simp] theorem conjugation_twice {Ω : Type*} (f : Ω → ℂ) :
    conjugation Ω (conjugation Ω f)=f := by funext x; exact star_star _

def conjugatedFrame {Ω : Type*} (F : Frame ℚ (Ω → ℂ)) : Frame ℚ (Ω → ℂ) :=
  ((conjugation Ω).trans F).trans (conjugation Ω)

@[simp] theorem conjugatedFrame_apply {Ω : Type*} (F : Frame ℚ (Ω → ℂ)) (f : Ω → ℂ) :
    conjugatedFrame F f=conjugation Ω (F (conjugation Ω f)) := rfl

@[simp] theorem conjugatedFrame_symm {Ω : Type*} (F : Frame ℚ (Ω → ℂ)) (f : Ω → ℂ) :
    (conjugatedFrame F).symm f=conjugation Ω (F.symm (conjugation Ω f)) := rfl

variable {ι Ω : Type*} [DecidableEq ι]

def bankConjugate (x : ι → Ω → ℂ) : ι → Ω → ℂ := fun i => conjugation Ω (x i)

omit [DecidableEq ι] in
@[simp] theorem bankConjugate_twice (x : ι → Ω → ℂ) :
    bankConjugate (bankConjugate x)=x := by
  funext i
  exact conjugation_twice _

/-- Every original rational scalar gate commutes with complex conjugation. -/
theorem gate_conjugate (g : Circuit.Gate ι ℚ) (x : ι → Ω → ℂ) :
    bankConjugate (moduleGate g x)=moduleGate g (bankConjugate x) := by
  funext i
  by_cases hi : i=g.target
  · subst i
    simp only [bankConjugate,moduleGate,Function.update_self,map_add]
    congr 1
    generalize g.terms=ps
    induction ps with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons,List.sum_cons,map_add,map_smul,ih]
  · simp only [bankConjugate,moduleGate,Function.update_of_ne hi]

def instruction : Instruction ι ℚ (Ω → ℂ) → Instruction ι ℚ (Ω → ℂ)
  | .edge i old next => .edge i (conjugatedFrame old) (conjugatedFrame next)
  | .gate g => .gate g

theorem execute_conjugate (ins : Instruction ι ℚ (Ω → ℂ)) (x : ι → Ω → ℂ) :
    bankConjugate (execute ins x)=execute (instruction ins) (bankConjugate x) := by
  cases ins with
  | gate g => exact gate_conjugate g x
  | edge j old next =>
    funext i
    by_cases hi : i=j
    · subst i
      simp only [execute,instruction,bankConjugate,Function.update_self,
        conjugatedFrame_apply,conjugatedFrame_symm,conjugation_twice]
    · simp only [execute,instruction,bankConjugate,Function.update_of_ne hi]

/-- The literal instruction order and scalar gates are unchanged. -/
theorem run_conjugate (p : List (Instruction ι ℚ (Ω → ℂ))) (x : ι → Ω → ℂ) :
    bankConjugate (run p x)=run (p.map instruction) (bankConjugate x) := by
  induction p generalizing x with
  | nil => rfl
  | cons ins p ih =>
    simpa only [run,List.map_cons,execute_conjugate] using ih (execute ins x)

theorem conjugated_run (p : List (Instruction ι ℚ (Ω → ℂ))) (x : ι → Ω → ℂ) :
    run (p.map instruction) x=bankConjugate (run p (bankConjugate x)) := by
  rw [run_conjugate]
  congr 1
  funext i
  exact (conjugation_twice _).symm

/-- The original complex25 network, with all its actual rational gates and
their original order, admits a faithful conjugate-oriented schedule. -/
def network (k : ℕ) := (ComplexFramedExecution.network k).map instruction

theorem network_length (k : ℕ) : (network k).length=(ComplexFramedExecution.network k).length :=
  List.length_map _

theorem network_run (k : ℕ) (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k) :
    run (network k) stored=fun i =>
      conjugatedFrame (ComplexFramedExecution.frameOf k
        (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector i))
        (ComplexFramedExecution.sign i •
          (conjugatedFrame (ComplexFramedExecution.frameOf k
            (GlobalLabels.source ComplexRank25.vector (ComplexFramedExecution.route i)))).symm
            (stored (ComplexFramedExecution.route i))) := by
  rw [network,conjugated_run,ComplexFramedExecution.network_run]
  funext i
  simp only [bankConjugate,conjugatedFrame_apply,conjugatedFrame_symm,
    map_smul,conjugation_twice]

/-- Negated-orientation source correction, defined by its exact array map. -/
def correctInput (k : ℕ) (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k) :=
  bankConjugate (ComplexEndpoints.correctInput k (bankConjugate stored))

/-- Negated-orientation sink correction, including the conjugated scalar phase
and the original signed bank rerouting. -/
def correctOutput (k : ℕ) (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k) :=
  bankConjugate (ComplexEndpoints.correctOutput k (bankConjugate stored))

/-- Conjugating only the internal edge phases is insufficient: the exact
original source and sink corrections are conjugated as well. The resulting
array run is the conjugate of the forward full tensor on conjugate input. -/
theorem corrected_network_run (k : ℕ)
    (stored : ComplexFramedExecution.Wire → BinaryColumns.Arrays (25^3) k) :
    correctOutput k (run (network k) (correctInput k stored))=fun i =>
      conjugation (BinaryColumns.Address (25^3) k)
        (ComplexEndpoints.fullFrame k (conjugation (BinaryColumns.Address (25^3) k) (stored i))) := by
  unfold correctInput correctOutput network
  rw [conjugated_run]
  simp only [bankConjugate_twice]
  rw [ComplexEndpoints.corrected_network_run]
  rfl

end
end IntegerMultBounds.Networks.ComplexFramedConjugation
