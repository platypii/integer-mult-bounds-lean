module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpInitializedGroup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpReleaseFrame

/-! # Release shared group setup once, restoring the entire original state except output -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def groupReleaseBase : Pr P 640 Q A U := .seq (uclear lineSymbols) release

private theorem high_off_banks (k : Fin 640) (hk : 369 ≤ k.val) :
    ∀ b ∈ allBanks, ∀ r, k ≠ b.rg r := by
  intro b hb r he
  have hr := allBanks_range b hb r
  have hv := congrArg Fin.val he
  omega

/-- A group's shared setup and symbol counter restore exactly; only its output survives. -/
theorem groupReleaseBase_exec (W p q l Γ w t s α m M : ℕ) (z : TblSt 16 A) (hz : z.acc = [])
    (v : HS 640 Q A U) (S SB : Stacks 640 A) (us : List (ZMod s → GaussianInt))
    (hinp : SB.inp = S.inp) (hout : SB.out = S.out) (hL : SB.L = S.L)
    (hframe : ∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k)
    (hbank0 : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [])
    (hwrite0 : ∀ k ∈ prepareWrites, S.R k = []) (hsymbols : S.R lineSymbols = [])
    (hsrc : tblHolds source SB (tblRho W (List.replicate W tick) (List.replicate w tick) z))
    (hbanks : ∀ b ∈ consumers, tblHolds b.rg SB
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) :
    let ST := symbolGroupResult p q l Γ w t s α m M SB us
    let SR := { ST with R := Function.update ST.R lineSymbols [] }
    ∃ v', v'.user = v.user ∧
      Exec body groupReleaseBase (mk v ST)
        ((2 * (s * w) + 2) + (clearPreparedCost SR.R + (218 * W + 12 * w + 243)))
        (mk v' { S with R := (Function.update S.R groupOutput
          ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) }) := by
  dsimp only
  let ST := symbolGroupResult p q l Γ w t s α m M SB us
  let SR : Stacks 640 A := { ST with R := Function.update ST.R lineSymbols [] }
  let ys := (us.map (groupLineOutput A s t α p)).flatten
  have hn : groupOutput ≠ lineSymbols := by decide +kernel
  have hlen : (ST.R lineSymbols).length = s * w := by
    simp only [ST, symbolGroupResult, symbolsPreparedStack, Function.update_of_ne hn.symm,
      Function.update_self, List.length_replicate]
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body lineSymbols v ST
  rw [hlen] at he₁
  have between (k : Fin 640) (hk : 176 ≤ k.val ∧ k.val < 369) : SR.R k = SB.R k := by
    have hs : k ≠ lineSymbols := by intro he; have hv := congrArg Fin.val he; change k.val = 543 at hv; omega
    have ho : k ≠ groupOutput := by intro he; have hv := congrArg Fin.val he; change k.val = 548 at hv; omega
    have hw : k ∉ prepareWrites := by
      intro h; have ho := prepareWrites_outside k h; omega
    simp only [SR, ST, symbolGroupResult, symbolsPreparedStack, Function.update_of_ne hs,
      Function.update_of_ne ho]
    exact preparedStack_off p q l Γ w t s α m M SB k hw
  obtain ⟨v₂, hu₂, he₂, hbank, hwrite⟩ := release_exec (body := body) W w z hz v₁ SR
    (fun r => (between _ (bank_range (ForwardBankPlacement.source r))).trans (hsrc r))
    (fun b hb r => (between _ (consumer_range b hb r)).trans (hbanks b hb r))
  have old (k : Fin 640) (hw : k ∉ prepareWrites)
      (hb : ∀ b ∈ allBanks, ∀ r, k ≠ b.rg r) :
      (preparedStack p q l Γ w t s α m M SB).R k = S.R k := by
    apply (preparedStack_off p q l Γ w t s α m M SB k hw).trans
    apply hframe k
    · exact hb ⟨16, source, id⟩ (by simp [allBanks])
    · exact fun b hm => hb b (List.mem_cons_of_mem _ hm)
  have hport : (symbolsPreparedStack p q l Γ w t s α m M SB).R groupOutput = S.R groupOutput := by
    change Function.update (preparedStack p q l Γ w t s α m M SB).R lineSymbols
      (List.replicate (s * w) tick) groupOutput = S.R groupOutput
    rw [Function.update_of_ne hn]
    exact old groupOutput (high_not_written _ (by decide +kernel))
      (high_off_banks _ (by decide +kernel))
  have heq : releasedStack SR = { S with R := Function.update S.R groupOutput (ys ++ S.R groupOutput) } := by
    apply releasedStack_eq_of_frame
      { S with R := Function.update S.R groupOutput (ys ++ S.R groupOutput) }
      SR hinp hout hL _ _ _ hbank hwrite
    · intro k hw hb
      by_cases hs : k = lineSymbols
      · subst k
        simpa only [SR, Function.update_self, Function.update_of_ne hn.symm] using hsymbols.symm
      by_cases ho : k = groupOutput
      · subst k
        simp only [SR, ST, symbolGroupResult, Function.update_of_ne hs, Function.update_self,
          hport, ys]
      · simp only [SR, ST, symbolGroupResult, symbolsPreparedStack, Function.update_of_ne hs,
          Function.update_of_ne ho]
        exact old k hw hb
    · intro b hb r
      have hne := high_off_banks groupOutput (by decide +kernel) b hb r
      simpa only [Function.update_of_ne hne.symm] using hbank0 b hb r
    · intro k hk
      have ho : k ≠ groupOutput := by
        intro he; have hv := congrArg Fin.val he; have := written_small k hk
        change k.val = 548 at hv
        omega
      simpa only [Function.update_of_ne ho] using hwrite0 k hk
  exact ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) heq)⟩

/-- Shared controls are erased once before releasing arithmetic setup. -/
def groupRelease : Pr P 640 Q A U := .seq controlsRelease groupReleaseBase

theorem groupRelease_exec (W p q l Γ w t s α m M : ℕ) (z : TblSt 16 A) (hz : z.acc = [])
    (v : HS 640 Q A U) (S SB : Stacks 640 A) (us : List (ZMod s → GaussianInt))
    (hinp : SB.inp = S.inp) (hout : SB.out = S.out) (hL : SB.L = S.L)
    (hframe : ∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k)
    (hbank0 : ∀ b ∈ allBanks, ∀ r, S.R (b.rg r) = [])
    (hwrite0 : ∀ k ∈ prepareWrites, S.R k = []) (hsymbols : S.R lineSymbols = [])
    (hcontrols : S.R (raw .count) = [] ∧ S.R (raw .control) = [])
    (hsrc : tblHolds source SB (tblRho W (List.replicate W tick) (List.replicate w tick) z))
    (hbanks : ∀ b ∈ consumers, tblHolds b.rg SB
      (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) :
    let ST := groupResult p q l Γ w t s α m M SB us
    let SL := symbolGroupResult p q l Γ w t s α m M SB us
    let SR := { SL with R := Function.update SL.R lineSymbols [] }
    ∃ v', v'.user = v.user ∧
      Exec body groupRelease (mk v ST)
        (controlsReleaseCost s t m w M +
          ((2 * (s * w) + 2) + (clearPreparedCost SR.R + (218 * W + 12 * w + 243))))
        (mk v' { S with R := (Function.update S.R groupOutput
          ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) }) := by
  dsimp only
  let ST := groupResult p q l Γ w t s α m M SB us
  have hn : (ST.R (raw .count)).length = M := by
    simp only [ST, groupResult, groupPreparedStack, controlsSetupR,
      Function.update_of_ne (show raw .count ≠ groupOutput by decide +kernel),
      Function.update_of_ne (raw_inj.ne (show ChirpRawReg.count ≠ .control by decide)),
      Function.update_self, List.length_replicate]
  have hc : ST.R (raw .control) = gatherControls A (chirpAdvancesFrom s t m w 0 M) := by
    simp only [ST, groupResult, groupPreparedStack, controlsSetupR,
      Function.update_of_ne (show raw .control ≠ groupOutput by decide +kernel), Function.update_self]
  obtain ⟨v₁, hu₁, he₁⟩ := controlsRelease_exec (body := body) s t m w M v ST hn hc
  have base (k : Fin 640) (hk : 500 ≤ k.val) (hs : k ≠ lineSymbols) (hz : S.R k = []) :
      (symbolsPreparedStack p q l Γ w t s α m M SB).R k = [] := by
    have hb := high_off_banks k (by omega)
    have hSB := hframe k (hb ⟨16, source, id⟩ (by simp [allBanks]))
      (fun b hm => hb b (List.mem_cons_of_mem _ hm))
    change Function.update (preparedStack p q l Γ w t s α m M SB).R lineSymbols _ k = []
    rw [Function.update_of_ne hs]
    exact (preparedStack_off p q l Γ w t s α m M SB k (high_not_written k hk)).trans (hSB.trans hz)
  have heq : { ST with R := controlsReleaseR ST.R } = symbolGroupResult p q l Γ w t s α m M SB us := by
    ext1
    · rfl
    · rfl
    · rfl
    exact controlsReleaseR_collect s t m w M (symbolsPreparedStack p q l Γ w t s α m M SB).R
      (us.map (groupLineOutput A s t α p)).flatten
      (base _ (by decide +kernel) (by decide +kernel) hcontrols.1)
      (base _ (by decide +kernel) (by decide +kernel) hcontrols.2)
  obtain ⟨v₂, hu₂, he₂⟩ := groupReleaseBase_exec (body := body) W p q l Γ w t s α m M z hz
    v₁ S SB us hinp hout hL hframe hbank0 hwrite0 hsymbols hsrc hbanks
  exact ⟨v₂, hu₂.trans hu₁,
    Exec.seq (he₁.cast rfl (congrArg (mk v₁) heq)) he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
