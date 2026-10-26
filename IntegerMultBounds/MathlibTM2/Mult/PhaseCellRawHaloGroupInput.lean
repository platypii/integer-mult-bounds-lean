module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellControlledHaloGroupInput

/-! Generate all class controls, gather the raw RHS and consume the owned halo
endpoint headers, yielding the exact closed solver input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def gatherHaloGroupInput : Pr P₀ 117 Q A U := .seq rawNaturalGather (clearWords [111,113])

def rawHaloGroupPrepare : Pr P₀ 117 Q A U :=
  .seq generateHaloOriginAndGatherControls gatherHaloGroupInput

def rawHaloGroupPrepareCost (P q s t u band a b L : ℕ) : ℕ :=
  generateHaloOriginAndGatherControlsCost P q s t u band a b L+rawNaturalGatherCost q s+2*(a+b)+5

theorem finishControlledHaloGroupInput_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hst : s < t)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (haloLengthGroup s t band a b L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C)))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawNaturalGatherCost q s+2*(a+b)+5 ∧
      Exec body gatherHaloGroupInput
        (mk v (controlledHaloGroupInputBank P N q l t u band a b L C borrowed outTail inp out)) n
        (mk v' (batchInputBank P N q l s t u band L B
          (fun n => (haloGroupOrigin s t band a b L n).val) rhs (raw++borrowed) outTail inp out)) := by
  dsimp only
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := gatherControlledHaloGroupInputBank_exec (body := body)
    P N q l s t u band a b L hst hgroup C v borrowed outTail inp out
  let B := (haloLengthGroup s t band a b L).length
  let raw := cstream A (2*q+8) (chirpLine s C)
  let rhs := cstream A (2*q+8) ((List.range B).flatMap
    (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C)))
  let S₂ := batchInputBank P N q l s t u band L B
    (fun n => (haloGroupOrigin s t band a b L n).val) rhs (raw++borrowed) outTail inp out
  let S₃ : Stacks 117 A := { S₂ with R := haloEndpointR a b S₂.R }
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [(111 : Fin 117),113] (by decide) v₂ S₃
  have hsum : (([(111 : Fin 117),113]).map (fun k => (S₃.R k).length)).sum = a+b := by
    simp [S₃,haloEndpointR]
  refine ⟨v₃,n₂+(2*(a+b)+5),hu₃.trans hu₂,by
    omega,
    (Exec.seq he₂ he₃).cast (by rw [hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h111 : k = 111
  · subst k; simp [batchInputBank]
  by_cases h113 : k = 113
  · subst k; simp [batchInputBank]
  simp [S₃,haloEndpointR,h111,h113,S₂,B,raw,rhs]

theorem rawHaloGroupInputBank_exec (P N q l s t u band a b L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (v : HS 117 Q A U)
    (borrowed outTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (haloLengthGroup s t band a b L).length
    let raw := cstream A (2*q+8) (chirpLine s C)
    let rhs := cstream A (2*q+8) ((List.range B).flatMap
      (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C)))
    ∃ v' n, v'.user = v.user ∧ n ≤ rawHaloGroupPrepareCost P q s t u band a b L ∧
      Exec body rawHaloGroupPrepare
        (mk v (haloGroupInputBank P N q l s t u band a b L raw borrowed outTail inp out)) n
        (mk v' (batchInputBank P N q l s t u band L B
          (fun n => (haloGroupOrigin s t band a b L n).val) rhs (raw++borrowed) outTail inp out)) := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateHaloGroupInputBank_exec (body := body)
    P N q l s t u band a b L hP hs hst hu hgroup hband has hbs hL hLs hA C v borrowed outTail inp out
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := finishControlledHaloGroupInput_exec (body := body)
    P N q l s t u band a b L hst hgroup C v₁ borrowed outTail inp out
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,by unfold rawHaloGroupPrepareCost; omega,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
