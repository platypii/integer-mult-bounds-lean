import IntegerMultBounds.Machine.PointwiseRoleGate

/-! Compile a fixed finite list of physical pointwise role gates. Every gate
shares the original descriptor and work clock and returns all payload heads
to their original positions, so sequential composition introduces no copying. -/
namespace IntegerMultBounds.Machine.PointwiseRoleCircuit
open PointwiseRoleGate (Gate bank applyGate)
variable {t a n : ℕ}
noncomputable section

def execute (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) :
    List (Gate t) → (Fin t → Fin n → Fin (a+4)) → (Fin t → Fin n → Fin (a+4))
  | [],data => data
  | g::gs,data => execute op gs (applyGate g op data)

def states : ℕ → ℕ
  | 0 => 1
  | n+1 => 36+states n

private def haltProgram (t a : ℕ) : Program (t+2) 1 a := ⟨by omega,0,fun _ _ => none⟩

def program (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) :
    (gs : List (Gate t)) → Program (t+2) (states gs.length) a
  | [] => haltProgram t a
  | g::gs => seq (PointwiseRoleGate.program g op) (program op gs)

/-- Exact full-bank correctness with one real join charged per fixed gate.
Tape count and finite control do not depend on runtime array length. -/
theorem circuit_hoare (op : Fin (a+4) → Fin (a+4) → Fin (a+4)) (gs : List (Gate t))
    (background : Fin t → ℤ → Fin (a+4)) (origins : Fin t → ℤ)
    (data : Fin t → Fin n → Fin (a+4)) (bs : List Bool) (hn : Counter.value bs = n) :
    HoareTime (program op gs) (fun w => w = bank background origins data bs)
      (fun w => w = bank background origins (execute op gs data) bs)
      (gs.length*(14*n+14*bs.length+34)) := by
  induction gs generalizing data with
  | nil => rintro w rfl; exact ⟨0,_,by simp,rfl,rfl,rfl⟩
  | cons g gs ih =>
    have hh := (PointwiseRoleGate.gate_hoare g op background origins data bs hn).seq
      (ih (applyGate g op data))
    exact hh.consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by simp only [List.length_cons]; ring))

theorem cost_linear (gs : List (Gate t)) (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    gs.length*(14*Counter.value bs+14*bs.length+34) ≤ gs.length*(28*Counter.value bs+48) := by
  have hh := PointwiseBinaryNormalized.cost_linear bs hc
  exact Nat.mul_le_mul_left gs.length (by omega)

theorem states_eq (k : ℕ) : states k = 36*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [states,ih]; omega

end
end IntegerMultBounds.Machine.PointwiseRoleCircuit
