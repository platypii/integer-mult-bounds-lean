module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpInitializedData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpPreparedGroup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupLineSymbols
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupControls

/-! # Initialize the shared setup once and execute the whole forward group -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

noncomputable def initializedGroup (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) : Pr P 640 Q A U :=
  .seq initialization (.seq lineSymbolsSetup (.seq controlsSetup (preparedGroup hQ hQrp true)))

def symbolsPreparedStack (p q l Γ w t s α m M : ℕ) (SB : Stacks 640 A) : Stacks 640 A :=
  let SF := preparedStack p q l Γ w t s α m M SB
  { SF with R := Function.update SF.R lineSymbols (List.replicate (s * w) tick) }

def groupPreparedStack (p q l Γ w t s α m M : ℕ) (SB : Stacks 640 A) : Stacks 640 A :=
  let SF := symbolsPreparedStack p q l Γ w t s α m M SB
  { SF with R := controlsSetupR s t m w M SF.R }

noncomputable def symbolGroupResult (p q l Γ w t s α m M : ℕ) (SB : Stacks 640 A)
    (us : List (ZMod s → GaussianInt)) : Stacks 640 A :=
  let SF := symbolsPreparedStack p q l Γ w t s α m M SB
  { SF with R := (Function.update SF.R groupOutput
    ((us.map (groupLineOutput A s t α p)).flatten ++ SF.R groupOutput)) }

noncomputable def groupResult (p q l Γ w t s α m M : ℕ) (SB : Stacks 640 A)
    (us : List (ZMod s → GaussianInt)) : Stacks 640 A :=
  let SF := groupPreparedStack p q l Γ w t s α m M SB
  { SF with R := (Function.update SF.R groupOutput
    ((us.map (groupLineOutput A s t α p)).flatten ++ SF.R groupOutput)) }

theorem initializedGroup_exec (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
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
    ∀ (us : List (ZMod s → GaussianInt)), (∀ u ∈ us, ∀ j, ‖value q (u j)‖ ≤ 1) →
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
    S.R (raw .raw) = [] →
    (∀ r, r ≠ .raw → r ≠ .dst → S.R (raw r) = []) →
    (rest : List (Fin (A + 4))) →
    (S.R lineCount).length = us.length →
    S.R groupInput = (us.map (groupLineInput A s α p)).flatten ++ rest →
    S.R lineSymbols = [] → S.R savedLineCount = [] →
    S.R inputArchive = [] → S.R outputArchive = [] →
    S.R groupBuf = [] → S.R groupTmp = [] →
    ∃ v' SB z n, v'.user = v.user ∧
      n ≤ initializeCost W b p q l Γ w t m M +
        (2 * tblC W w + (6 * (s * w) + 11 * W + 7)) +
        (controlsSetupCost W w s t m M +
        ((us.map (fun u => groupLineCost A s t α p u true)).sum + 5 * us.length +
          2 * (us.map (groupLineInput A s α p)).flatten.length +
          2 * (us.map (groupLineOutput A s t α p)).flatten.length + 8)) ∧
      Exec body (initializedGroup hQ hQrp) (mk v S) n
        (mk v' (groupResult p q l Γ w t s α m M SB us)) ∧
      tblHolds source SB (tblRho W (List.replicate W tick) (List.replicate w tick) z) ∧
      (∀ b ∈ consumers, tblHolds b.rg SB
        (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) ∧
      z.acc = [] ∧ SB.inp = S.inp ∧ SB.out = S.out ∧ SB.L = S.L ∧
      (∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k) ∧
      SelectedLineData s t α p (preparedStack p q l Γ w t s α m M SB) := by
  dsimp only
  intro us hu v S hwidth hwords hzero hsource hconsumers hproc hcr hnr hclean hK0
    hbank hproducer hring hworkspace hdim hoperand hraw0 hraw rest hcount hinput
    hsymbols hsaved harchive houtputs hbuf htmp
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let M := chirpBlockCount t m
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  obtain ⟨v₁, SB, z, n₁, hu₁, hn₁, he₁, hsrc, hbanks, hz, hzacc, hframe⟩ :=
    initialize_exec (body := body) s t α p hst hα hαp v S hwidth hwords hzero hsource hconsumers
  let SF := preparedStack p q l Γ w t s α m M SB
  have hd := initialized_lineData W p q l Γ w t s α m S SB z
    hframe.2.2.1 hframe.2.2.2.1 hbanks hz hproc hcr hnr hclean hK0 hbank
    hproducer hring hworkspace hdim hoperand hraw
  have off (k : Fin 640) (hk : 533 ≤ k.val) : SF.R k = S.R k :=
    initialized_off p q l Γ w t s α m M S SB hframe.2.2.2.1 k
      (Or.inr (by omega)) (high_not_written k (by omega))
  have hsrcF : tblHolds source SF (tblRho W (List.replicate W tick) (List.replicate w tick) z) := by
    intro r
    exact (preparedStack_bank p q l Γ w t s α m M SB (ForwardBankPlacement.source r)).trans (hsrc r)
  have hp : 1 ≤ p := hα.trans ((Nat.le_mul_self α).trans (by simpa only [pow_two] using hαp))
  rcases chirpForwardCaller_fits s t p α hp hαp with
    ⟨_, _, _, hwW, _, _, _, _, _, hvolume, htm, hproduct, _⟩
  have hvol : s * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (show s ≤ s + 3 * m + 1 by omega)).trans_lt hvolume
  rcases hz with ⟨_, _, hzm, hzM, _, _, _, hzw, hz0, hzs, hzt, hzfit⟩
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := lineSymbolsSetup_exec (body := body)
    W w s hwW hvol z hzs hzw hz0 hzfit v₁ SF hsrcF
  let ST := symbolsPreparedStack p q l Γ w t s α m M SB
  have he₂' : Exec body lineSymbolsSetup (mk v₁ SF) n₂ (mk v₂ ST) := by
    change Exec body lineSymbolsSetup (mk v₁ SF) n₂
      (mk v₂ { SF with R := Function.update SF.R lineSymbols (List.replicate (s * w) tick) })
    have hsF : SF.R lineSymbols = [] := (off lineSymbols (by decide +kernel)).trans hsymbols
    simpa only [hsF, List.append_nil] using he₂
  have htframe (k : Fin 640) (hk : k ≠ lineSymbols) : ST.R k = SF.R k := by
    exact Function.update_of_ne hk _ _
  have hdT : SelectedLineData s t α p ST := by
    apply hd.frame (S' := ST) rfl
    intro k hk
    apply htframe
    intro he
    have hv := congrArg Fin.val he
    change k.val = 543 at hv
    omega
  have e (k : Fin 640) (hk : 533 ≤ k.val) (hn : k ≠ lineSymbols) : ST.R k = S.R k :=
    (htframe k hn).trans (off k hk)
  have hrawT : ST.R (raw .raw) = [] :=
    (htframe _ (by decide +kernel)).trans
      ((initialized_off p q l Γ w t s α m M S SB hframe.2.2.2.1 _
        (raw_outside_banks .raw) (raw_not_written .raw)).trans hraw0)
  have hstep (j : ℕ) (hj : j < M) : (j + 1) * m ≤ t + m :=
    (Nat.mul_le_mul_right m (Nat.succ_le_of_lt hj)).trans (chirpBlockCount_mul_le t m)
  have hgfit : ∀ i : Fin 4, (![s, t, m, w] : Fin 4 → ℕ) i < 2 ^ W := by
    intro i
    fin_cases i
    · change s < 2 ^ W
      simpa only [hzs] using hzfit 14
    · change t < 2 ^ W
      simpa only [hzt] using hzfit 15
    · change m < 2 ^ W
      simpa only [hzm] using hzfit 5
    · change w < 2 ^ W
      simpa only [hzw] using hzfit 11
  have hsrcT : tblHolds source ST (tblRho W (List.replicate W tick) (List.replicate w tick) z) := by
    intro r
    apply (htframe _ ?_).trans (hsrcF r)
    intro he
    have hv := congrArg Fin.val he
    have hb := bank_range (ForwardBankPlacement.source r)
    change (bankTape (ForwardBankPlacement.source r)).val = 543 at hv
    omega
  obtain ⟨vC, nC, huC, hnC, heC⟩ := controlsSetup_exec (body := body) W w s t m M hwW hst.le
    (NeZero.pos t) (fun j hj => (hstep j hj).trans_lt htm)
    (fun j hj => (Nat.mul_le_mul_left s (hstep j hj)).trans_lt hproduct)
    ((Nat.mul_le_mul_right w (show m ≤ s + 3 * m + 1 by omega)).trans_lt hvolume)
    z hzM hzfit hgfit v₂ ST hsrcT hdT.gather (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> apply hdT.raw <;> decide)
  let SC := groupPreparedStack p q l Γ w t s α m M SB
  have heC' : Exec body controlsSetup (mk v₂ ST) nC (mk vC SC) := by
    change Exec body controlsSetup (mk v₂ ST) nC
      (mk vC { ST with R := controlsSetupR s t m w M ST.R })
    exact heC
  have hdC : SelectedLineData s t α p SC true := hdT.shareControls
  have scOff (k : Fin 640) (hk : 533 ≤ k.val) : SC.R k = ST.R k := by
    change controlsSetupR s t m w M ST.R k = ST.R k
    exact controlsSetupR_high s t m w M ST.R k hk
  have eC (k : Fin 640) (hk : 533 ≤ k.val) (hn : k ≠ lineSymbols) : SC.R k = S.R k :=
    (scOff k hk).trans (e k hk hn)
  have hrawC : SC.R (raw .raw) = [] :=
    (controlsSetupR_off s t m w M ST.R _ (by decide +kernel) (by decide +kernel)).trans hrawT
  obtain ⟨v₃, n₃, hu₃, hn₃, he₃⟩ := preparedGroup_exec (shared := true) (body := body)
    hQ hQrp hA s t α p hst hα hαp us hu vC SC rest hdC
    (by simpa only [eC lineCount (by decide +kernel) (by decide +kernel)] using hcount)
    (by simpa only [eC groupInput (by decide +kernel) (by decide +kernel)] using hinput)
    (by simp only [scOff lineSymbols (by decide +kernel), ST, symbolsPreparedStack, Function.update_self, List.length_replicate, w, q, l, Γ])
    hrawC
    (by simpa only [eC groupBuf (by decide +kernel) (by decide +kernel)] using hbuf)
    (by simpa only [eC groupTmp (by decide +kernel) (by decide +kernel)] using htmp)
    (by simpa only [eC savedLineCount (by decide +kernel) (by decide +kernel)] using hsaved)
    (by simpa only [eC inputArchive (by decide +kernel) (by decide +kernel)] using harchive)
    (by simpa only [eC outputArchive (by decide +kernel) (by decide +kernel)] using houtputs)
  refine ⟨v₃, SB, z, n₁ + (n₂ + (nC + n₃)), hu₃.trans (huC.trans (hu₂.trans hu₁)), by
      simpa only [Nat.add_assoc, W, w, q, l, Γ, m, M] using
        Nat.add_le_add hn₁ (Nat.add_le_add hn₂ (Nat.add_le_add hnC hn₃)),
    Exec.seq he₁ (Exec.seq he₂' (Exec.seq heC' he₃)), hsrc, hbanks, hzacc,
    hframe.1, hframe.2.1, hframe.2.2.1, hframe.2.2.2.2, hd⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
