module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders

/-! The key loop changes only its owned queue/count and ambient output.
The private-bank release frame collapses because each iteration starts clean. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Node

def keyLoopR {A : ℕ} (R : Regs 144 A) (keys count output : List (Fin (A+4))) : Regs 144 A :=
  Function.update (Function.update (Function.update R 126 keys) 127 count) 132 output

theorem keyLoopR_off {A : ℕ} (R : Regs 144 A) (keys count output : List (Fin (A+4)))
    (k : Fin 144) (hk126 : k ≠ 126) (hk127 : k ≠ 127) (hk132 : k ≠ 132) :
    keyLoopR R keys count output k = R k := by simp [keyLoopR,hk126,hk127,hk132]

theorem keyLoopR_comp {A : ℕ} (R : Regs 144 A) (keys count output keys' count' output' : List (Fin (A+4))) :
    keyLoopR (keyLoopR R keys count output) keys' count' output' = keyLoopR R keys' count' output' := by
  funext k
  by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h132 : k = 132 <;>
    simp [keyLoopR,Function.update_apply,h126,h127,h132]

theorem keyLoopR_self {A : ℕ} (R : Regs 144 A) : keyLoopR R (R 126) (R 127) (R 132) = R := by
  funext k
  by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;> by_cases h132 : k = 132 <;>
    simp_all [keyLoopR]

theorem publishedClassR_clean {A : ℕ} (R : Regs 144 A) (output : List (Fin (A+4)))
    (h128 : R 128 = []) (h129 : R 129 = []) (h140 : R 140 = []) :
    publishedClassR R output = Function.update R 132 output := by
  funext k
  by_cases hk128 : k = 128
  · subst k; simp [publishedClassR,h128]
  by_cases hk129 : k = 129
  · subst k; simp [publishedClassR,h129]
  by_cases hk132 : k = 132
  · subst k; simp [publishedClassR]
  by_cases hk140 : k = 140
  · subst k; simp [publishedClassR,h140]
  simp [publishedClassR,hk128,hk129,hk132,hk140]

theorem keyLoopR_step {A : ℕ} (R : Regs 144 A) (keys count output : List (Fin (A+4)))
    (h128 : R 128 = []) (h129 : R 129 = []) (h140 : R 140 = []) :
    publishedClassR (Function.update (Function.update R 127 count) 126 keys) output = keyLoopR R keys count output := by
  rw [publishedClassR_clean _ output (by simpa using h128) (by simpa using h129) (by simpa using h140)]
  funext k
  by_cases h126 : k = 126 <;> by_cases h127 : k = 127 <;>
    simp [keyLoopR,Function.update_apply,h126,h127]

theorem groupHeaderSources_off (r : Fin 144 × Fin 144) (hr : r ∈ groupHeaderCopies) :
    r.1 ≠ 126 ∧ r.1 ≠ 127 ∧ r.1 ≠ 132 := by
  simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem keyLoopR_headers {A : ℕ} (R : Regs 144 A) (keys count output : List (Fin (A+4)))
    (value : Fin 144 → ℕ) (h : ∀ r ∈ groupHeaderCopies, (R r.1).length = value r.1) :
    ∀ r ∈ groupHeaderCopies, (keyLoopR R keys count output r.1).length = value r.1 := by
  intro r hr
  obtain ⟨h126,h127,h132⟩ := groupHeaderSources_off r hr
  rw [keyLoopR_off R keys count output r.1 h126 h127 h132]
  exact h r hr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
