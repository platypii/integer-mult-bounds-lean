module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledHaloGroupInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProbeAndGatherHaloControls

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

def probedHaloGroupInputBank {A s : ℕ} (P N q l t u band a b L : ℕ)
    (C : ZMod s → GaussianInt) (borrowed outTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  if 0 < (haloLengthGroup s t band a b L).length then
    controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out else
    haloGroupInputBank P N q l s t u band a b L (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out

theorem probeHaloGroupInputBank_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ v'.flag = decide (0 < (haloLengthGroup s t band a b L).length) ∧ n ≤ probeAndGatherHaloControlsCost P q s t u band a b L ∧
      Exec body probeAndGatherHaloControls
        (mk v (haloGroupInputBank P N q l s t u band a b L
          (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out)) n
        (mk v' (probedHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out)) := by
  let w := 2*q+8
  let raw := cstream A w (chirpLine s C)
  let S := haloGroupInputBank P N q l s t u band a b L raw borrowed outTail inp out
  obtain ⟨v₁, n₁, hu₁, hflag₁, hn₁, he₁⟩ := probeAndGatherHaloControls_exec (body := body)
    P q s t u band a b L hP hs hst hu hband has hbs hL hLs hA v S
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by
      intro k hk
      have hn (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, Fin.ext_iff, hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 111 (by decide), hn 113 (by decide), hn 109 (by decide), hn 112 (by decide), hn 114 (by decide),
        hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
  refine ⟨v₁,n₁,hu₁,hflag₁,hn₁,he₁.cast rfl ?_⟩
  congr 1
  by_cases hB : 0 < (haloLengthGroup s t band a b L).length
  · simp only [probedHaloGroupInputBank,probedHaloGatherR,ite_eq_left hB]
    rfl
  · simp only [probedHaloGroupInputBank,probedHaloGatherR,ite_eq_right hB]
    rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
