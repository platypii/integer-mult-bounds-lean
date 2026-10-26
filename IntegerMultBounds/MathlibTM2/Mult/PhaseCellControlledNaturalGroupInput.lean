module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawNaturalGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupInput

/-! The generated-control handoff in raw group preparation. Keeping this
intermediate bank explicit permits protected publication setup before gathering. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def controlledNaturalGroupInputBank {A s : ℕ} (P N q l t u band L : ℕ)
    (C : ZMod s → GaussianInt) (borrowed outTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := naturalGroupInputBank P N q l s t u band L
    (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out
  { S with R := originAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band L (2*q+8) S.R }

theorem generateNaturalGroupInputBank_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (hband : band ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateOriginAndGatherControlsCost P q s t u band L ∧
      Exec body generateOriginAndGatherControls
        (mk v (naturalGroupInputBank P N q l s t u band L
          (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out)) n
        (mk v' (controlledNaturalGroupInputBank P N q l t u band L C borrowed outTail inp out)) := by
  let w := 2*q+8
  let raw := cstream A w (chirpLine s C)
  let S := naturalGroupInputBank P N q l s t u band L raw borrowed outTail inp out
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := generateOriginAndGatherControls_exec (body := body)
    P q s t u band L hP hs hst hu hgroup hband hL hLs hA v S
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
  exact ⟨v₁,n₁,hu₁,hn₁,he₁⟩

theorem gatherControlledNaturalGroupInputBank_exec (P N q l s t u band L : ℕ) [NeZero s]
    (hst : s < t) (hgroup : 0 < (naturalLengthGroup s t band L).length)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (naturalLengthGroup s t band L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C)))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawNaturalGatherCost q s ∧
      Exec body rawNaturalGather
        (mk v (controlledNaturalGroupInputBank P N q l t u band L C borrowed outTail inp out)) n
        (mk v' (batchInputBank P N q l s t u band L B
          (fun n => (naturalGroupOrigin s t band L n).val) rhs (raw++borrowed) outTail inp out)) := by
  dsimp only
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let raw := cstream A w (chirpLine s C)
  let S := naturalGroupInputBank P N q l s t u band L raw borrowed outTail inp out
  let S₁ : Stacks 117 A := { S with R := originAndGatherControlsR A V s t band L w S.R }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := rawNaturalGather_exec (body := body)
    q t band L hst hgroup C borrowed v S₁
    (by simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank])
    (by simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank])
    (by simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank])
    (by simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank, raw, w])
    (by simp [S₁, originAndGatherControlsR, S, naturalGroupInputBank, batchInputBank, w]) (by
      intro k hk
      have hn (n : ℕ) (hn : 11 ≤ n) : k.val ≠ n := by omega
      simp [S₁, originAndGatherControlsR, originControlsR, Fin.ext_iff,
        S, naturalGroupInputBank, batchInputBank,
        hn 91 (by decide), hn 109 (by decide), hn 116 (by decide), hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 112 (by decide), hn 114 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank])
  refine ⟨v₂,n₂,hu₂,hn₂,he₂.cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h109 : k = 109
    · subst k
      simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank,
        naturalOriginPackets_eq_rows, V, w]
    by_cases h116 : k = 116
    · subst k; simp [S₁, originAndGatherControlsR, originControlsR, batchInputBank]
    by_cases h110 : k = 110
    · subst k
      simp [S₁, originAndGatherControlsR, originControlsR, S, naturalGroupInputBank, batchInputBank, w, raw]
    by_cases h91 : k = 91
    · subst k; simp [batchInputBank]
    simp [S₁, originAndGatherControlsR, originControlsR, Fin.ext_iff,
      S, naturalGroupInputBank, batchInputBank,
      show k.val ≠ 109 from fun he => h109 (Fin.ext he), show k.val ≠ 116 from fun he => h116 (Fin.ext he),
      show k.val ≠ 110 from fun he => h110 (Fin.ext he), show k.val ≠ 91 from fun he => h91 (Fin.ext he)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
