module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlCleanup

/-! # Generate gathering controls and restore the complete setup bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

def chirpControlBatch (rg : TblR 10 → Fin T) (count saved acc dst : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR count)) <|
  .seq (.loop (·.flag) (chirpControlLoopBody rg count saved acc)) <|
  .seq (tblCompile rg tblChirpControlClear) <|
  .seq (moveR saved count id) (moveR acc dst id)

/-- Compute every advance packet from dimensions, retaining only the generated stream. -/
theorem chirpControlBatch_exec (hrg : Function.Injective rg) (count saved acc dst : Fin T)
    (hreg : [count, saved, acc, dst].Nodup) (hcount : ∀ r, rg r ≠ count)
    (hsaved : ∀ r, rg r ≠ saved) (hacc : ∀ r, rg r ≠ acc) (hdst : ∀ r, rg r ≠ dst)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (s t m w M : ℕ) (hst : s ≤ t) (ht : 0 < t)
    (hk : ∀ j < M, (j + 1) * m < 2 ^ W)
    (hnum : ∀ j < M, s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (st : TblSt 10 A) (hready : ChirpControlReady st s t m w 0)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (hlen : (S.R count).length = M) (hs0 : S.R saved = []) (ha0 : S.R acc = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (6 * tblC W e + 11 * W + 14) +
        (4 * W + 4) * (chirpCenter s t m M * w) + 6 * tblC W e + 6 ∧
      Exec body (chirpControlBatch rg count saved acc dst) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (gatherControls A (chirpAdvancesFrom s t m w 0 M) ++ S.R dst)) }) := by
  classical
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨st₁, v₁, S₁, n₁, hr₁, ha₁, hfit₁, hu₁, hn₁, he₁, hb₁, hc₁, hs₁, hd₁,
    hi₁, ho₁, hl₁, hf₁⟩ := chirpControlLoop_exec (body := body) hrg count saved acc (by regs_nodup)
      hcount hsaved hacc wl nl hwl hnl heW s t m w 0 M hst ht
      (by simpa only [Nat.zero_add] using hk) (by simpa only [Nat.zero_add] using hnum)
      hwidth st hready hfit (S.R count) hlen { v with flag := (S.R count).head?.isSome } S hS rfl rfl
  obtain ⟨st₂, ⟨hv₂, ha₂⟩, hclear⟩ :=
    (tblChirpControlClear_do (W := W) (e := e) st st₁ s t m w M hready
      (by simpa using hr₁) hzero).host (body := body) hrg wl nl hwl hnl heW hfit₁
  have hst₂ : st₂ = st := by
    have ha : st₂.acc = st.acc := ha₂.trans ha₁
    cases st₂; cases st
    simp_all only
  subst st₂
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hb₂, hf₂⟩ := hclear v₁ S₁ hb₁
  have off (k : Fin T) (hoff : ∀ r, rg r ≠ k) : S₂.R k = S₁.R k := hf₂.2.2.2 k hoff
  have hcount₂ : S₂.R count = [] := (off count hcount).trans hc₁
  have hsaved₂ : S₂.R saved = (S.R count).reverse := by rw [off saved hsaved, hs₁, hs0, List.append_nil]
  have hacc₂ : S₂.R acc = (gatherControls A (chirpAdvancesFrom s t m w 0 M)).reverse := by
    rw [off acc hacc, hd₁, ha0, List.append_nil]
  have hdst₂ : S₂.R dst = S.R dst := by
    rw [off dst hdst, hf₁ dst ‹count ≠ dst›.symm ‹saved ≠ dst›.symm ‹acc ≠ dst›.symm hdst]
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved count ‹count ≠ saved›.symm id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R saved count id (S₂.R saved) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body acc dst ‹acc ≠ dst› id v₃ S₃
  let S₄ : Stacks T A := { S₃ with R := movedR S₃.R acc dst id (S₃.R acc) }
  have hp := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hp
  have hsteps : 1 + (n₁ + (n₂ + ((2 * (S₂.R saved).length + 2) + (2 * (S₃.R acc).length + 2)))) ≤
      M * (6 * tblC W e + 11 * W + 14) + (4 * W + 4) * (chirpCenter s t m M * w) +
        6 * tblC W e + 6 := by
    have hacc₃ : S₃.R acc = S₂.R acc := by simp [S₃, movedR, ‹saved ≠ acc›.symm, ‹count ≠ acc›.symm]
    rw [hacc₃, hacc₂, hsaved₂, List.length_reverse, List.length_reverse, hlen, length_gatherControls]
    rw [chirpControlLoopCost_eq, chirpAdvances_sum] at hn₁
    have hM : (chirpAdvancesFrom s t m w 0 M).length = M := by simp [chirpAdvancesFrom]
    rw [hM] at hn₁ ⊢
    calc _ ≤ 1 + (M * (6 * tblC W e + 11 * W + 10) +
        (4 * W + 2) * (chirpCenter s t m M * w) + 1 +
        (6 * tblC W e + ((2 * M + 2) + (2 * (chirpCenter s t m M * w + M) + 2)))) := by
          rw [chirpAdvances_sum]
          omega
      _ = _ := by ring
  have hex := Exec.seq hp (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))
  refine ⟨v₄, _, hu₄.trans (hu₃.trans (hu₂.trans hu₁)), hsteps, hex.cast rfl ?_⟩
  congr 1
  have hstack : S₄ = { S with R := (Function.update S.R dst
      (gatherControls A (chirpAdvancesFrom s t m w 0 M) ++ S.R dst)) } := by
    ext1
    · exact hf₂.1.trans hi₁
    · exact hf₂.2.1.trans ho₁
    · exact hf₂.2.2.1.trans hl₁
    funext k
    by_cases hkd : k = dst
    · subst k
      simp [S₄, S₃, movedR, ‹count ≠ acc›.symm, ‹saved ≠ acc›.symm,
        ‹count ≠ dst›.symm, ‹saved ≠ dst›.symm, hacc₂, hdst₂]
    by_cases hkc : k = count
    · subst k
      simp [S₄, S₃, movedR, ‹count ≠ acc›, ‹count ≠ dst›,
        hsaved₂, hcount₂]
    by_cases hks : k = saved
    · subst k
      simp [S₄, S₃, movedR, ‹saved ≠ acc›, ‹saved ≠ dst›, ‹count ≠ saved›.symm, hs0]
    by_cases hka : k = acc
    · subst k
      simp [S₄, movedR, ‹acc ≠ dst›, ha0]
    simp only [S₄, S₃, movedR, Function.update_of_ne hkd, Function.update_of_ne hka,
      Function.update_of_ne hkc, Function.update_of_ne hks]
    by_cases hbank : ∃ r, rg r = k
    · obtain ⟨r, rfl⟩ := hbank
      exact (hb₂ r).trans (hS r).symm
    · have hoff : ∀ r, rg r ≠ k := by simpa using hbank
      exact (off k hoff).trans (hf₁ k hkc hks hka hoff)
  exact hstack

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
