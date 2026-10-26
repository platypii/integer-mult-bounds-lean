module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloGatherControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawHaloGather
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

def haloEndpointR {A : ℕ} (a b : ℕ) (R : Fin 117 → List (Fin (A+4))) :=
  Function.update (Function.update R 111 (List.replicate a tick)) 113 (List.replicate b tick)

def haloGroupInputBank {A : ℕ} (P N q l s t u band a b L : ℕ)
    (rhs borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := naturalGroupInputBank P N q l s t u band L rhs borrowed outTail inp out
  { S with R := haloEndpointR a b S.R }

def controlledHaloGroupInputBank {A s : ℕ} (P N q l t u band a b L : ℕ)
    (C : ZMod s → GaussianInt) (borrowed outTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) : Stacks 117 A :=
  let S := haloGroupInputBank P N q l s t u band a b L
    (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out
  { S with R := haloOriginAndGatherControlsR A (weightWorkspaceWidth P q (2*q+8) t u) s t band a b L (2*q+8) S.R }

theorem generateHaloGroupInputBank_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateHaloOriginAndGatherControlsCost P q s t u band a b L ∧
      Exec body generateHaloOriginAndGatherControls
        (mk v (haloGroupInputBank P N q l s t u band a b L
          (cstream A (2*q+8) (chirpLine s C)) borrowed outTail inp out)) n
        (mk v' (controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out)) := by
  let w := 2*q+8
  let raw := cstream A w (chirpLine s C)
  let S := haloGroupInputBank P N q l s t u band a b L raw borrowed outTail inp out
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := generateHaloOriginAndGatherControls_exec (body := body)
    P q s t u band a b L hP hs hst hu hgroup hband has hbs hL hLs hA v S
    (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank]) (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by
      intro k hk
      have hn (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, Fin.ext_iff, hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 111 (by decide), hn 113 (by decide), hn 109 (by decide), hn 112 (by decide), hn 114 (by decide),
        hn 116 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [haloEndpointR,S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
  exact ⟨v₁,n₁,hu₁,hn₁,he₁⟩

theorem gatherControlledHaloGroupInputBank_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hst : s < t) (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (haloLengthGroup s t band a b L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C)))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawNaturalGatherCost q s ∧
      Exec body rawNaturalGather
        (mk v (controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out)) n
        (mk v' (let S := (batchInputBank P N q l s t u band L B
          (fun n => (haloGroupOrigin s t band a b L n).val) rhs (raw++borrowed) outTail inp out);
          { S with R := haloEndpointR a b S.R })) := by
  dsimp only
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let raw := cstream A w (chirpLine s C)
  let S := haloGroupInputBank P N q l s t u band a b L raw borrowed outTail inp out
  let S₁ : Stacks 117 A := { S with R := haloOriginAndGatherControlsR A V s t band a b L w S.R }
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := rawHaloGather_exec (body := body)
    q t band a b L hst hgroup C borrowed v S₁
    (by simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
    (by simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, raw, w])
    (by simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, w]) (by
      intro k hk
      have hn (n : ℕ) (hn : 11 ≤ n) : k.val ≠ n := by omega
      simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, Fin.ext_iff,
        S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, Fin.ext_iff,
        hn 91 (by decide), hn 109 (by decide), hn 116 (by decide), hn 101 (by decide), hn 102 (by decide),
        hn 103 (by decide), hn 97 (by decide), hn 98 (by decide), hn 99 (by decide),
        hn 100 (by decide), hn 111 (by decide), hn 113 (by decide), hn 112 (by decide), hn 114 (by decide), hn 110 (by decide), hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank])
  refine ⟨v₂,n₂,hu₂,hn₂,he₂.cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h109 : k = 109
    · subst k
      simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, Fin.ext_iff,
        haloOriginPackets_eq_rows, V, w]
    by_cases h116 : k = 116
    · subst k; simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, batchInputBank]
    by_cases h110 : k = 110
    · subst k
      simp [haloEndpointR,S₁, haloOriginAndGatherControlsR, haloClassControlsR, S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, w, raw]
    by_cases h91 : k = 91
    · subst k; simp [haloEndpointR,batchInputBank]
    by_cases h111 : k = 111
    · subst k; simp [haloEndpointR,S₁,haloOriginAndGatherControlsR,haloClassControlsR,S,haloGroupInputBank,naturalGroupInputBank,batchInputBank]
    by_cases h113 : k = 113
    · subst k; simp [haloEndpointR,S₁,haloOriginAndGatherControlsR,haloClassControlsR,S,haloGroupInputBank,naturalGroupInputBank,batchInputBank]
    simp [haloEndpointR,h111,h113,S₁, haloOriginAndGatherControlsR, haloClassControlsR, Fin.ext_iff,
      S, haloGroupInputBank, haloEndpointR, naturalGroupInputBank, batchInputBank, Fin.ext_iff,
      show k.val ≠ 109 from fun he => h109 (Fin.ext he), show k.val ≠ 116 from fun he => h116 (Fin.ext he),
      show k.val ≠ 110 from fun he => h110 (Fin.ext he), show k.val ≠ 91 from fun he => h91 (Fin.ext he)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
