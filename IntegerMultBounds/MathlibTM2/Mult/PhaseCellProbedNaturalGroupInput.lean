module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledNaturalGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbeAndGatherControls

/-! Ordinary parameters produce either the controlled nonempty bank or the
unchanged ordinary bank, with the actual row count exposed in the branch flag. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def probedNaturalGroupInputBank {A s : ℕ} (P N q l t u band L : ℕ)
    (C : ZMod s → GaussianInt) (borrowed outTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  if 0 < (naturalLengthGroup s t band L).length then
    controlledNaturalGroupInputBank P N q l t u band L C borrowed outTail inp out else
    naturalGroupInputBank P N q l s t u band L (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out

theorem probeNaturalGroupInputBank_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ v'.flag = decide (0 < (naturalLengthGroup s t band L).length) ∧ n ≤ probeAndGatherControlsCost P q s t u band L ∧
      Exec body probeAndGatherControls
        (mk v (naturalGroupInputBank P N q l s t u band L
          (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out)) n
        (mk v' (probedNaturalGroupInputBank P N q l t u band L C borrowed outTail inp out)) := by
  let w := 2*q+8
  let raw := cstream A w (chirpLine s C)
  let S := naturalGroupInputBank P N q l s t u band L raw borrowed outTail inp out
  obtain ⟨v₁, n₁, hu₁, hflag₁, hn₁, he₁⟩ := probeAndGatherControls_exec (body := body)
    P q s t u band L hP hs hst hu hband hL hLs hA v S
    (by simp [S, naturalGroupInputBank, batchInputBank]) (by simp [S, naturalGroupInputBank, batchInputBank])
    (by simp [S, naturalGroupInputBank, batchInputBank]) (by simp [S, naturalGroupInputBank, batchInputBank])
    (by simp [S, naturalGroupInputBank, batchInputBank]) (by simp [S, naturalGroupInputBank, batchInputBank])
    (by simp [S, naturalGroupInputBank, batchInputBank]) (by
      intro k hk
      have hn (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simp [S, naturalGroupInputBank, batchInputBank, hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 109 (by decide), hn 112 (by decide), hn 114 (by decide),
        hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S, naturalGroupInputBank, batchInputBank])
  refine ⟨v₁,n₁,hu₁,hflag₁,hn₁,he₁.cast rfl ?_⟩
  congr 1
  by_cases hB : 0 < (naturalLengthGroup s t band L).length
  · simp only [probedNaturalGroupInputBank,probedGatherR,ite_eq_left hB]
    rfl
  · simp only [probedNaturalGroupInputBank,probedGatherR,ite_eq_right hB]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
