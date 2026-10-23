module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlHost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherWindows

/-! # Generate the complete gathering-control stream with one fixed loop -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

def chirpControlLoopBody (rg : TblR 10 → Fin T) (count saved dst : Fin T) : Pr P T Q A U :=
  .seq (.act (popPush count saved)) (.seq (chirpControlNext rg dst) (.act (peekR count)))

def chirpControlLoopCost (W e : ℕ) (ds : List ℕ) : ℕ :=
  (ds.map (fun d => 6 * tblC W e + W * (4 * d + 11) + 2 * d + 10)).sum + 1

/-- Structural loop over the actual unary block count, computing every packet at runtime. -/
theorem chirpControlLoop_exec (hrg : Function.Injective rg) (count saved dst : Fin T)
    (hreg : [count, saved, dst].Nodup) (hcount : ∀ r, rg r ≠ count)
    (hsaved : ∀ r, rg r ≠ saved) (hdst : ∀ r, rg r ≠ dst)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (s t m w j M : ℕ) (hst : s ≤ t) (ht : 0 < t)
    (hk : ∀ i < M, (j + i + 1) * m < 2 ^ W)
    (hnum : ∀ i < M, s * ((j + i + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (st : TblSt 10 A) (hready : ChirpControlReady st s t m w j) (hfit : ∀ i, st.val i < 2 ^ W)
    (cs : List (Fin (A + 4))) (hlen : cs.length = M)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (hc : S.R count = cs) (hflag : v.flag = cs.head?.isSome) :
    ∃ (st' : TblSt 10 A) (v' : HS T Q A U) (S' : Stacks T A) (n : ℕ),
      ChirpControlReady st' s t m w (j + M) ∧ st'.acc = st.acc ∧
      (∀ i, st'.val i < 2 ^ W) ∧ v'.user = v.user ∧
      n ≤ chirpControlLoopCost W e (chirpAdvancesFrom s t m w j M) ∧
      Exec body (.loop (·.flag) (chirpControlLoopBody rg count saved dst)) (mk v S) n (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl st') ∧ S'.R count = [] ∧
      S'.R saved = cs.reverse ++ S.R saved ∧
      S'.R dst = (gatherControls A (chirpAdvancesFrom s t m w j M)).reverse ++ S.R dst ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ k, k ≠ count → k ≠ saved → k ≠ dst → (∀ r, rg r ≠ k) → S'.R k = S.R k) := by
  have hreg' := hreg
  regs_ne hreg'
  induction M generalizing j st cs v S with
  | zero =>
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [hnil] at hflag
    refine ⟨st, v, S, 1, by simpa using hready, rfl, hfit, rfl, by simp [chirpControlLoopCost, chirpAdvancesFrom],
      Exec.loop_false (by simpa using hflag), hS, hc.trans hnil, by simp [hnil], by simp [chirpAdvancesFrom, gatherControls],
      rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | succ M ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      let S₀ : Stacks T A := { S with R := Function.update (Function.update S.R count cs) saved (c :: S.R saved) }
      let v₀ : HS T Q A U := { v with sym := some c }
      have hpop : (popPush count saved : Act T Q A U).run (mk v S) = mk v₀ S₀ := by
        simp [popPush, Action.run, update_rt, hc, S₀, v₀, ‹count ≠ saved›.symm]
      have hbank₀ : tblHolds rg S₀ (tblRho W wl nl st) := by
        intro r
        simpa only [S₀, Function.update_of_ne (hsaved r), Function.update_of_ne (hcount r)] using hS r
      obtain ⟨st₁, v₁, S₁, n₁, hr₁, ha₁, hfit₁, hu₁, hn₁, he₁, hb₁, hd₁, hi₁, ho₁, hl₁, hf₁⟩ :=
        chirpControlNext_exec (body := body) hrg dst hdst wl nl hwl hnl heW st s t m w j
          hready hst ht (by simpa using hk 0 (by omega)) (by simpa using hnum 0 (by omega))
          hwidth hfit v₀ S₀ hbank₀
      have hc₁ : S₁.R count = cs := by
        rw [hf₁ count ‹count ≠ dst› hcount]
        simp [S₀, ‹count ≠ saved›]
      have hs₁ : S₁.R saved = c :: S.R saved := by
        rw [hf₁ saved ‹saved ≠ dst› hsaved]
        simp [S₀]
      have hd₀ : S₀.R dst = S.R dst := by
        simp [S₀, ‹count ≠ dst›.symm, ‹saved ≠ dst›.symm]
      have hp := Exec.act (body := body) (peekR count) (mk v₁ S₁)
      rw [peekR_run, hc₁] at hp
      obtain ⟨st₂, v₂, S₂, n₂, hr₂, ha₂, hfit₂, hu₂, hn₂, he₂, hb₂, hc₂, hs₂, hd₂,
        hi₂, ho₂, hl₂, hf₂⟩ := ih (j + 1)
        (by intro i hi; simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hk (i + 1) (by omega))
        (by intro i hi; simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hnum (i + 1) (by omega))
        st₁ hr₁ hfit₁ cs (by simpa using hlen)
        { v₁ with flag := cs.head?.isSome } S₁ hb₁ hc₁ rfl
      have he : Exec body (chirpControlLoopBody rg count saved dst) (mk v S) (n₁ + 2)
          (mk { v₁ with flag := cs.head?.isSome } S₁) :=
        (Exec.seq (hpop ▸ Exec.act (body := body) (popPush count saved) _) (Exec.seq he₁ hp)).cast (by omega) rfl
      refine ⟨st₂, v₂, S₂, n₁ + 2 + n₂ + 1, by simpa only [Nat.add_assoc, Nat.add_comm 1 M] using hr₂,
        ha₂.trans ha₁, hfit₂, hu₂.trans hu₁, ?_, Exec.loop_true (by simpa using hflag) he he₂,
        hb₂, hc₂, ?_, ?_, hi₂.trans hi₁, ho₂.trans ho₁, hl₂.trans hl₁, ?_⟩
      · rw [chirpAdvancesFrom_succ]
        simp only [chirpControlLoopCost, List.map_cons, List.sum_cons] at hn₂ ⊢
        omega
      · rw [hs₂, hs₁, List.reverse_cons, List.append_assoc, List.singleton_append]
      · rw [hd₂, hd₁, hd₀, chirpAdvancesFrom_succ]
        simp only [gatherControls, List.reverse_append, List.reverse_cons, List.reverse_replicate,
          List.append_assoc, List.cons_append, List.nil_append]
      · intro k hkc hks hkd hoff
        rw [hf₂ k hkc hks hkd hoff, hf₁ k hkd hoff]
        simp [S₀, hkc, hks]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
