module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpInitializedData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpSelectedFixedLine
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardSelected

/-! # Execute initialization and the fixed forward line from original scalar and line inputs

Retained setup remains allocated for subsequent lines. No prepared arithmetic,
coefficient bank, numerical gate or register layout is supplied by the caller.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

noncomputable def initializedLine (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) : Pr P 640 Q A U :=
  .seq initialization (program hQ hQrp)

def lineResult (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A) (u : ZMod s → GaussianInt) : Stacks 640 A :=
  let SF := preparedStack p q l Γ w t s α m M S
  { SF with R := (Function.update SF.R (output.nr .out)
    (cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u))) }

noncomputable def readOutput (p wo t : ℕ) (S : Stacks 640 A) : ZMod t → ℂ :=
  fun k => value p (decodeWord (((S.R (output.nr .out)).drop (k.val * wo)).take wo))

theorem read_lineResult (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A) (u : ZMod s → GaussianInt) :
    readOutput p (p + l + Γ + 5) t (lineResult p q l Γ w t s α m M S u) =
      chirpForwardDecoded A s t α p q l Γ m u := by
  funext k
  simp only [readOutput, lineResult, Function.update_self, chirpForwardDecoded, List.append_nil]

/-- Decoding the actual returned tape has the selected forward-resampling error bound. -/
theorem lineResult_error (hA : 4 ≤ A) (s t α p : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    ∀ (S : Stacks 640 A) (u : ZMod s → GaussianInt), (∀ j, ‖value q (u j)‖ ≤ 1) →
      2 ^ p * ‖readOutput p (p + l + Γ + 5) t (lineResult p q l Γ w t s α m (chirpBlockCount t m) S u) -
        IntegerMultBounds.NLogN.resampA s t (α : ℝ) (fun j => value q (u j))‖ ≤ 4 := by
  dsimp only
  intro S u hu
  have he := chirpForwardSelected_error (A := A) hA hst α p hα hαp u hu
  rw [read_lineResult]
  exact he

/-- A fixed program computes the selected forward output from raw words and a retained raw line. -/
theorem initializedLine_exec (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
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
    ∃ v' SB z n, v'.user = v.user ∧
      n ≤ initializeCost W b p q l Γ w t m M +
        (chirpRawCorrelationCost W w W w s t q l m w + chirpOutputCompleteCost (M * m) p q l Γ w t) ∧
      Exec body (initializedLine hQ hQrp) (mk v S) n
        (mk v' (lineResult p q l Γ w t s α m M SB u)) ∧
      tblHolds source SB (tblRho W (List.replicate W tick) (List.replicate w tick) z) ∧
      (∀ b ∈ consumers, tblHolds b.rg SB
        (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) ∧
      z.acc = [] ∧ SB.inp = S.inp ∧ SB.out = S.out ∧ SB.L = S.L ∧
      (∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k) ∧
      2 ^ p * ‖readOutput p (p + l + Γ + 5) t (lineResult p q l Γ w t s α m M SB u) -
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
  let B := chirpForwardCallerBase s t p
  let W := chirpForwardTableWord q B
  obtain ⟨v₁, SB, z, n₁, hu₁, hn₁, he₁, hsrc, hbanks, hz, hzacc, hframe⟩ :=
    initialize_exec (body := body) s t α p hst hα hαp v S hwidth hwords hzero hsource hconsumers
  let SF := preparedStack p q l Γ w t s α m M SB
  have hd := initialized_lineData W p q l Γ w t s α m S SB z
    hframe.2.2.1 hframe.2.2.2.1 hbanks hz hproc hcr hnr hclean hK0 hbank
    hproducer hring hworkspace hdim hoperand hraw
  have hinputF : SF.R (raw .raw) = cstream A w (chirpLine s u) :=
    (initialized_off p q l Γ w t s α m M S SB hframe.2.2.2.1 _
      (raw_outside_banks .raw) (raw_not_written .raw)).trans hinput
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := SelectedLineData.exec (body := body)
    hQ hQrp hA s t α p hst hα hαp u hu v₁ SF hd hinputF
  exact ⟨v₂, SB, z, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂, Exec.seq he₁ he₂,
    hsrc, hbanks, hzacc, hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.2,
    lineResult_error (by omega) s t α p hst hα hαp SB u hu⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
