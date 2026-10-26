module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeLengthKeysReady

/-! Release the iterator's retained widths. Once the counted loop has restored
its queue suffix, only the published ambient output differs from the input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

def releasedKeyRuntimeR {A : ℕ} (R : Regs 144 A) : Regs 144 A :=
  fun k => if k ∈ [(125 : Fin 144),130] then [] else R k

theorem released_keyLoop_initialized {A : ℕ} (R : Regs 144 A) (V w K : ℕ)
    (keys output : List (Fin (A+4)))
    (h125 : R 125 = []) (h127 : R 127 = []) (h130 : R 130 = []) :
    releasedKeyRuntimeR (keyLoopR (initializedKeyRuntimeR R V w K keys) (R 126) [] output) =
      Function.update R 132 output := by
  funext k
  by_cases h125k : k = 125
  · subst k; simp [releasedKeyRuntimeR,h125]
  by_cases h130k : k = 130
  · subst k; simp [releasedKeyRuntimeR,h130]
  by_cases h126k : k = 126
  · subst k; simp [releasedKeyRuntimeR,keyLoopR]
  by_cases h127k : k = 127
  · subst k; simp [releasedKeyRuntimeR,keyLoopR,h127]
  by_cases h132k : k = 132
  · subst k; simp [releasedKeyRuntimeR,keyLoopR]
  simp [releasedKeyRuntimeR,keyLoopR,initializedKeyRuntimeR,
    h125k,h130k,h126k,h127k,h132k]

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 144 Q A U}

def releaseKeyRuntime : Pr P₀ 144 Q A U := clearWords [125,130]

theorem releaseKeyRuntime_exec (V w : ℕ) (v : HS 144 Q A U) (S : Stacks 144 A)
    (h125 : (S.R 125).length = V) (h130 : (S.R 130).length = w) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseKeyRuntime (mk v S) (2*(V+w)+5)
        (mk v' { S with R := releasedKeyRuntimeR S.R }) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(125 : Fin 144),130] (by decide) v S
  refine ⟨v',hu,he.cast ?_ rfl⟩
  simp [h125,h130]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
