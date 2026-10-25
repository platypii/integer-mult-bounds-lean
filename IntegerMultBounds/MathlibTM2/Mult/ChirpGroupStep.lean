module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupArchive

/-! # One executed forward line inside a group with shared setup -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

/-- Stage, execute and collect one line, retaining all shared setup. -/
noncomputable def groupStep (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (shared : Bool := false) : Pr P 640 Q A U :=
  .seq stageLine (.seq (programWith shared hQ hQrp) collectLine)

def groupStepR (xs rest ys : List (Fin (A + 4))) (R : Regs 640 A) : Regs 640 A :=
  Function.update (Function.update (Function.update R groupInput rest)
    inputArchive (xs.reverse ++ R inputArchive)) outputArchive (ys.reverse ++ R outputArchive)

theorem groupStep_exec {shared : Bool} (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
    ∀ (u : ZMod s → GaussianInt) (_hu : ∀ j, ‖value q (u j)‖ ≤ 1)
      (v : HS 640 Q A U) (S : Stacks 640 A) (rest : List (Fin (A + 4))),
      let xs := cstream A w (chirpLine s u)
      let ys := cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u)
      SelectedLineData s t α p S shared → S.R groupInput = xs ++ rest →
      (S.R lineSymbols).length = xs.length → S.R (raw .raw) = [] →
      S.R groupBuf = [] → S.R groupTmp = [] →
      ∃ v' n, v'.user = v.user ∧
        n ≤ chirpRawCorrelationModeCost shared W w W w s t q l m w +
          chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t +
          16 * xs.length + 2 * ys.length + 18 ∧
        Exec body (groupStep hQ hQrp shared) (mk v S) n
          (mk v' { S with R := groupStepR xs rest ys S.R }) := by
  dsimp only
  intro u hu v S rest h hi hc hr hb ht
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let xs := cstream A w (chirpLine s u)
  let ys := cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u)
  obtain ⟨v₁, hu₁, he₁⟩ := stageLine_exec (body := body) v S xs rest hi hc hr hb ht
  let S₁ : Stacks 640 A := { S with R := stageLineR xs rest S.R }
  have hd : SelectedLineData s t α p S₁ shared := h.stage xs rest
  have hx : S₁.R (raw .raw) = xs := by simp only [S₁, stageLineR, Function.update_self]
  obtain ⟨v₂, n, hu₂, hn, he₂⟩ := SelectedLineData.exec (shared := shared) (body := body)
    hQ hQrp hA s t α p hst hα hαp u hu v₁ S₁ hd hx
  let S₂ : Stacks 640 A := { S₁ with R := Function.update S₁.R (output.nr .out) ys }
  have hx₂ : S₂.R (raw .raw) = xs := by
    simpa only [S₂, Function.update_of_ne (show raw .raw ≠ output.nr .out by decide +kernel)] using hx
  have hy₂ : S₂.R (output.nr .out) = ys := by simp only [S₂, Function.update_self]
  obtain ⟨v₃, hu₃, he₃⟩ := collectLine_exec (body := body) v₂ S₂ xs ys hx₂ hy₂
  have ho : S.R (output.nr .out) = [] := h.outputState.nr_empty .out (by simp)
  have hf : collectLineR ys S₂.R = groupStepR xs rest ys S.R :=
    group_roundTrip xs rest ys S.R hr ho
  refine ⟨v₃, 14 * xs.length + 14 + (n + (2 * xs.length + 2 * ys.length + 4)),
    hu₃.trans (hu₂.trans hu₁), by
      dsimp only [xs, ys, w, q, l, Γ, m] at *
      omega, ?_⟩
  have he := Exec.seq he₁ (Exec.seq he₂ he₃)
  simpa only [groupStep, S₂, S₁, hf] using he

/-- Every line/setup tape is unchanged after a collected group step. -/
theorem groupStepR_low (xs rest ys : List (Fin (A + 4))) (R : Regs 640 A)
    (k : Fin 640) (hk : k.val < 533) : groupStepR xs rest ys R k = R k := by
  have hi : k ≠ groupInput := by
    intro he; have hv := congrArg Fin.val he; change k.val = 540 at hv; omega
  have ha : k ≠ inputArchive := by
    intro he; have hv := congrArg Fin.val he; change k.val = 541 at hv; omega
  have ho : k ≠ outputArchive := by
    intro he; have hv := congrArg Fin.val he; change k.val = 542 at hv; omega
  simp only [groupStepR, Function.update_of_ne ho, Function.update_of_ne ha, Function.update_of_ne hi]

/-- The same prepared data is ready for the following grouped line. -/
theorem LineData.groupStep {shared : Bool} {W s t α p q l Γ m w : ℕ} {S : Stacks 640 A}
    (h : LineData W s t α p q l Γ m w S shared) (xs rest ys : List (Fin (A + 4))) :
    LineData W s t α p q l Γ m w { S with R := groupStepR xs rest ys S.R } shared := by
  apply h.frame (S' := { S with R := groupStepR xs rest ys S.R }) rfl
  exact fun k hk => groupStepR_low xs rest ys S.R k hk.1

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
