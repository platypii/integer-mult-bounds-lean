module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineRestoration

/-! # The raw-input forward line with complete setup release and original-state restoration -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

noncomputable def closedLine (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) : Pr P 640 Q A U :=
  .seq (initializedLine hQ hQrp) release

/-- One fixed raw-input program restores the whole original state except its returned output tape. -/
theorem closedLine_exec (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let M := chirpBlockCount t m
    let B := chirpForwardCallerBase s t p
    let W := chirpForwardTableWord q B
    let b := Nat.size B
    ∀ (u : ZMod s → GaussianInt), (∀ j, ‖value q (u j)‖ ≤ 1) →
    ∀ (v : HS 640 Q A U) (S : Stacks 640 A),
    (S.R wordWidth).length = W →
    (∀ i : Fin 4, S.R (scalarInput i.castSucc) = binSyms b ((![p, α, s, t] : Fin 4 → ℕ) i)) →
    S.R (scalarInput 4) = [] → (∀ r, S.R (source r) = []) →
    (∀ b ∈ consumers, ∀ r, S.R (b.rg r) = []) →
    (∀ r, S.R (processor r) = []) → (∀ r, S.R (output.cr r) = []) →
    (∀ r, S.R (output.nr r) = []) → CClean output.mul S → S.R (batch .srcY) = [] →
    (∀ i, S.R (output.bank i) = []) → (∀ i, S.R (producer i) = []) →
    RpClean host S → (∀ k ∈ correlationEmpty, S.R k = []) →
    (∀ i, S.R (correlationDimensions i) = []) → S.R (batch .srcX) = [] →
    S.R (raw .raw) = cstream A w (chirpLine s u) →
    (∀ r, r ≠ .raw → r ≠ .dst → S.R (raw r) = []) →
    ∃ (v' : HS 640 Q A U) (SB : Stacks 640 A) (n : ℕ), v'.user = v.user ∧
      n ≤ (initializeCost W b p q l Γ w t m M +
        (chirpRawCorrelationCost W w W w s t q l m w + chirpOutputCompleteCost (M * m) p q l Γ w t)) +
        (clearPreparedCost (lineResult p q l Γ w t s α m M SB u).R + (218 * W + 12 * w + 243)) ∧
      Exec body (closedLine hQ hQrp) (mk v S) n
        (mk v' { S with R := (Function.update S.R (output.nr .out)
          (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) }) ∧
      2 ^ p * ‖readOutput p (p + l + Γ + 5) t
        { S with R := (Function.update S.R (output.nr .out)
          (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) } -
        IntegerMultBounds.NLogN.resampA s t (α : ℝ) (fun j => value q (u j))‖ ≤ 4 := by
  dsimp only
  intro u hu v S hwidth hwords hzero hsource hconsumers hproc hcr hnr hclean hK0
    hbank hproducer hring hworkspace hdim hoperand hinput hraw
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let M := chirpBlockCount t m
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  obtain ⟨v₁, SB, z, n₁, hu₁, hn₁, he₁, hsrc, hbanks, hzacc, hinp, hout, hL, hframe, herr⟩ :=
    initializedLine_exec (body := body) hQ hQrp hA s t α p hst hα hαp u hu v S hwidth hwords hzero
      hsource hconsumers hproc hcr hnr hclean hK0 hbank hproducer hring hworkspace hdim hoperand hinput hraw
  obtain ⟨v₂, hu₂, he₂, hzeroBanks, hzeroWrites⟩ := release_lineResult_exec (body := body)
    W p q l Γ w t s α m M z hzacc v₁ SB u hsrc hbanks
  have hfresh : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [] := by
    intro b hb r
    rcases List.mem_cons.mp hb with he | hb
    · subst b; exact hsource r
    · exact hconsumers b hb r
  have heq := released_lineResult_eq p q l Γ w t s α m M S SB u hinp hout hL hframe hfresh
    (prepareWrites_fresh S hproc hcr hnr hK0 hbank) hzeroBanks hzeroWrites
  refine ⟨v₂, SB, _, hu₂.trans hu₁, Nat.add_le_add_right hn₁ _,
    (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) heq), ?_⟩
  rw [← heq, releasedStack_readOutput]
  exact herr

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
