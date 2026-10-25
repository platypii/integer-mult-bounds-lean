module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRoleCode
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvFixed

/-! # Scalar multiplication on the existing 117-tape phase-cell bank

The 64 private multiplier tapes and thirty arithmetic roles reuse S1's released
workspace. Original dimensions, operands and the persistent output remain outside
this arithmetic footprint. Counter generation is a separate executed setup step.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Node

/-- Reuse the established thirty-role encoding. Role 9 is moved past the output ports. -/
def cr (r : CR) : Fin 117 :=
  let c := (OutputPlacement.code r).val
  ⟨if c = 9 then 95 else if c < 10 then 84 + c else 54 + c, by
    have hc := (OutputPlacement.code r).isLt
    split_ifs <;> omega⟩

def mul (i : Fin 64) : Fin 117 := ⟨i.val, by omega⟩

theorem cr_injective : Function.Injective cr := by
  intro r s h
  apply OutputPlacement.code_injective
  apply Fin.ext
  have hv := congrArg Fin.val h
  have hr := (OutputPlacement.code r).isLt
  have hs := (OutputPlacement.code s).isLt
  simp only [cr] at hv
  split_ifs at hv <;> omega

theorem mul_injective : Function.Injective mul := by
  intro i j h
  have hv := congrArg (fun k : Fin 117 => k.val) h
  exact Fin.ext hv

theorem cr_range (r : CR) : 64 ≤ (cr r).val ∧ (cr r).val ≤ 95 ∧
    (cr r).val ≠ 93 ∧ (cr r).val ≠ 94 := by
  have hr := (OutputPlacement.code r).isLt
  simp only [cr]
  split_ifs <;> omega

theorem cr_mul (r : CR) (i : Fin 64) : cr r ≠ mul i := by
  intro h
  have hh := congrArg Fin.val h
  have hr := (cr_range r).1
  have hi := i.isLt
  simp only [mul] at hh
  omega

/-- Every scalar role is fresh after the merged-branch execution. -/
theorem cr_fresh {A : ℕ} (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) (r : CR) :
    (Fixed.start q l w M L L X V tail inp out).R (cr r) = [] := by
  obtain ⟨_, hr, h93, h94⟩ := cr_range r
  simp [Fixed.start, Fixed.inputBank, h93, h94,
    show (cr r).val ≠ 100 by omega, show (cr r).val ≠ 101 by omega,
    show (cr r).val ≠ 102 by omega, show (cr r).val ≠ 103 by omega,
    show (cr r).val ≠ 108 by omega, show (cr r).val ≠ 110 by omega,
    show (cr r).val ≠ 111 by omega]

theorem mul_clean {A : ℕ} (q l w M L : ℕ) (X V : ℕ → List GaussianInt)
    (tail : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    CClean mul (Fixed.start q l w M L L X V tail inp out) := by
  intro i
  have hi := i.isLt
  constructor
  · rfl
  · simp [Fixed.start, Fixed.inputBank, mul,
      show i.val ≠ 94 by omega, show i.val ≠ 100 by omega,
      show i.val ≠ 101 by omega, show i.val ≠ 102 by omega,
      show i.val ≠ 103 by omega, show i.val ≠ 108 by omega,
      show i.val ≠ 110 by omega, show i.val ≠ 111 by omega, show i.val ≠ 93 by omega]

/-- The exact readiness bank that executed setup must construct. -/
def counterR {A : ℕ} (q w : ℕ) (R : Regs 117 A) : Regs 117 A :=
  Function.update (Function.update (Function.update R (cr .wn) (List.replicate w tick))
    (cr .pn) (List.replicate q tick)) (cr .nn) (List.replicate (Schoenhage.Schedule.topN w) tick)

/-- These three generated counters suffice; all operand/output roles may then be supplied. -/
theorem counterR_ready_of_work {A : ℕ} (q w : ℕ) (R : Regs 117 A)
    (hblank : ∀ r, r ∉ [CR.xs, .ys, .out] → R (cr r) = []) :
    Ready (fun r => counterR q w R (cr r)) w q := by
  constructor <;> simp [counterR, cr_injective.eq_iff]
  all_goals exact hblank _ (by decide)

theorem counterR_ready {A : ℕ} (q w : ℕ) (R : Regs 117 A) (hblank : ∀ r, R (cr r) = []) :
    Ready (fun r => counterR q w R (cr r)) w q :=
  counterR_ready_of_work q w R (fun r _ => hblank r)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
