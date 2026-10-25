module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupRelease
public import IntegerMultBounds.MathlibTM2.Mult.ChirpFastCost
public import IntegerMultBounds.MathlibTM2.Cost.ChirpForwardBudget

/-! # The raw-input group with one initialization and complete final release -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Cost

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

noncomputable def closedGroup (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) : Pr P 640 Q A U :=
  .seq (initializedGroup hQ hQrp) groupRelease

/-- Generate shared setup once, execute every line, then restore everything except the published group. -/
theorem closedGroup_exec (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
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
    ∃ (v' : HS 640 Q A U) (n : ℕ), v'.user = v.user ∧
      n ≤ selectedGroupCost s t α p us.length ∧
      n ≤ selectedGroupFastCost s t α p us.length ∧
      (n : ℝ) ≤ chirpGroupAllowance s t α p us.length ∧
      (p ^ 2 ≤ t → (W + 1) ^ 3 ≤ us.length →
        (n : ℝ) ≤ chirpForwardCostConstant * (us.length : ℝ) * (t : ℝ) *
          (p : ℝ) ^ (129 / 128 : ℝ)) ∧
      Exec body (closedGroup hQ hQrp) (mk v S) n
        (mk v' { S with R := (Function.update S.R groupOutput
          ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) }) ∧
      GroupOutputError s t α p us
        { S with R := (Function.update S.R groupOutput
          ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) } := by
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
  obtain ⟨v₁, SB, z, n₁, hu₁, hn₁, he₁, hsrc, hbanks, hzacc, hinp, hout, hL, hframe, hdata⟩ :=
    initializedGroup_exec (body := body) hQ hQrp hA s t α p hst hα hαp us hu v S
      hwidth hwords hzero hsource hconsumers hproc hcr hnr hclean hK0 hbank hproducer
      hring hworkspace hdim hoperand hraw0 hraw rest hcount hinput hsymbols hsaved
      harchive houtputs hbuf htmp
  have hfresh : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [] := by
    intro b hb r
    rcases List.mem_cons.mp hb with he | hb
    · subst b; exact hsource r
    · exact hconsumers b hb r
  obtain ⟨v₂, hu₂, he₂⟩ := groupRelease_exec (body := body) W p q l Γ w t s α m M z hzacc
    v₁ S SB us hinp hout hL hframe hfresh
    (prepareWrites_fresh S hproc hcr hnr hK0 hbank) hsymbols
    ⟨hraw .count (by decide) (by decide), hraw .control (by decide) (by decide)⟩ hsrc hbanks
  have hrc : clearPreparedCost (Function.update
      (symbolGroupResult p q l Γ w t s α m M SB us).R lineSymbols []) =
      retainedReleaseCost p q l Γ w t m M := by
    dsimp only [symbolGroupResult, symbolsPreparedStack]
    rw [clearPreparedCost_update_high _ lineSymbols (by decide +kernel),
      clearPreparedCost_update_high _ groupOutput (by decide +kernel),
      clearPreparedCost_update_high _ lineSymbols (by decide +kernel)]
    exact hdata.clearPreparedCost (by dsimp [q, chirpForwardPrecision]; omega) (Nat.le_refl _)
  let n := n₁ + (controlsReleaseCost s t m w M + ((2 * (s * w) + 2) +
    (clearPreparedCost (Function.update (symbolGroupResult p q l Γ w t s α m M SB us).R lineSymbols []) +
      (218 * W + 12 * w + 243))))
  have hn : n ≤ selectedGroupCost s t α p us.length := by
    let setup := fun n => initializeCost W (Nat.size (chirpForwardCallerBase s t p)) p q l Γ w t m M +
      (2 * tblC W w + (6 * (s * w) + 11 * W + 7)) + (controlsSetupCost W w s t m M + n)
    have hn' : n₁ ≤ setup (groupRunBound s t α p us.length true) :=
      hn₁.trans_eq (congrArg setup (groupRunCost_eq (shared := true) A s t α p hα us))
    have hcleanup := congrArg (fun n => controlsReleaseCost s t m w M +
      ((2 * (s * w) + 2) + (n + (218 * W + 12 * w + 243)))) hrc
    exact Nat.add_le_add hn' hcleanup.le
  have hnReal : (n : ℝ) ≤ (selectedGroupCost s t α p us.length : ℝ) := by exact_mod_cast hn
  exact ⟨v₂, n, hu₂.trans hu₁, hn,
    hn.trans (selectedGroupCost_le_fast s t α p us.length hst hα),
    hnReal.trans (chirp_selected_allowance_le s t α p us.length hst hα hαp),
    fun ht hN => hnReal.trans (chirp_selected_amortized_budget s t α p us.length hst hα hαp ht hN),
    Exec.seq he₁ he₂,
    fun i => publishedGroup_error (by omega) hst α p hα hαp us hu S i⟩


end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
