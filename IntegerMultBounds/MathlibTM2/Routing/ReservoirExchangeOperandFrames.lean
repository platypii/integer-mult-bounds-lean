module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirExchangeOperands

/-! Fixed register placement connects generated reservoir scalars to the
three exchange-frame encoders, without supplying their starts or spans. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def reservoirExchangeFrameSlot (k stage : Fin 3) : Fin 10 → Fin 22 :=
  if stage = 0 then
    ![6, (if k = 0 then 15 else if k = 1 then 8 else 9),
      (if k = 0 then 16 else 17), 19, 20, 18, 10, 11, 12, 13]
  else if stage = 1 then ![2, 4, 21, 19, 20, 18, 10, 11, 12, 13]
  else ![3, 5, 21, 19, 20, 18, 10, 11, 12, 13]

theorem reservoirExchangeFrameSlot_injective (k stage : Fin 3) :
    Function.Injective (reservoirExchangeFrameSlot k stage) := by
  fin_cases k <;> fin_cases stage <;> decide +kernel

theorem reservoirExchangeFrameSlot_destination (k stage : Fin 3) :
    reservoirExchangeFrameSlot k stage 5 = 18 := by
  fin_cases stage <;> simp [reservoirExchangeFrameSlot]

theorem reservoirExchangeOperandBank_read
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 22 → Fin T)
    (hrg : Function.Injective rg) (L n H w : ℕ) (j : Fin 22) :
    reservoirExchangeOperandBank R rg L n H w (rg j) =
      match j.val with
      | 3 => binSyms L (2 * w)
      | 4 => binSyms L (n - 2 * w)
      | 5 => binSyms L (n - w)
      | 6 => binSyms L 0
      | 7 => binSyms L (2 * H)
      | 8 => binSyms L (3 * H)
      | 9 => binSyms L (6 * H)
      | 15 => binSyms L 0
      | 16 => binSyms L 0
      | 17 => binSyms L (3 * H)
      | 21 => binSyms L w
      | _ => R (rg j) := by
  fin_cases j <;> simp [reservoirExchangeOperandBank, reservoirExchangeOperandJobs, hrg.eq_iff]

/-- Generated operands provide all three exact exchange specifications. -/
theorem reservoirExchangeOperandFrames_ready
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 22 → Fin T)
    (hrg : Function.Injective rg) (L n H w : ℕ) (hfit : 9 * H ≤ n) (hw : w ≤ H)
    (hspan : R (rg 2) = binSyms L w) (k stage : Fin 3) :
    let B := reservoirExchangeOperandBank R rg L n H w
    let slot := reservoirExchangeFrameSlot k stage
    B (rg (slot 0)) = binSyms L (reservoirExchangeSpecs n H hfit w hw k stage).a ∧
    B (rg (slot 1)) = binSyms L (reservoirExchangeSpecs n H hfit w hw k stage).b ∧
    B (rg (slot 2)) = binSyms L (reservoirExchangeSpecs n H hfit w hw k stage).w := by
  dsimp only
  simp_rw [reservoirExchangeOperandBank_read R rg hrg]
  fin_cases k <;> fin_cases stage <;>
    simp [reservoirExchangeFrameSlot, reservoirExchangeSpecs, reservoirFrontSpec, hspan,
      Nat.mul_comm, Nat.mul_left_comm]

/-- Frame arithmetic uses only scratch tapes left blank by operand generation. -/
theorem reservoirExchangeOperandFrames_blank
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 22 → Fin T)
    (hrg : Function.Injective rg) (L n H w : ℕ)
    (hblank : ∀ j : Fin 22, j = 19 ∨ j = 20 ∨ j = 10 ∨ j = 11 ∨ j = 12 → R (rg j) = [])
    (k stage : Fin 3) (i : Fin 10) (hi : i = 3 ∨ i = 4 ∨ i = 6 ∨ i = 7 ∨ i = 8) :
    reservoirExchangeOperandBank R rg L n H w (rg (reservoirExchangeFrameSlot k stage i)) = [] := by
  rw [reservoirExchangeOperandBank_read R rg hrg]
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    fin_cases stage <;> simp [reservoirExchangeFrameSlot] <;> apply hblank <;> decide

end IntegerMultBounds.MathlibTM2.Routing
