module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceHostStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceFrameStock
public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! The arbitrary ordered origin scan shares one arithmetic reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def originAdvanceLoopWorkspace (W e w previous : ℕ) (origins : List ℕ) : ℕ :=
  3*tblC W e+75*W+19*(originAdvances w previous origins).sum+64*origins.length+63

theorem originAdvanceLoop_exec_within {W e previous w : ℕ} (he : e ≤ W)
    (origins : List ℕ) (hsorted : (previous::origins).Pairwise (· ≤ ·))
    (hcoords : ∀ origin ∈ origins, origin < 2^W) (hunits : ∀ origin ∈ origins, origin*w < 2^W)
    (st : TblSt 4 A) (hp : st.val 1 = previous) (hw : st.val 2 = w) (hfit : ∀ i, st.val i < 2^W)
    (cs suffix : List (Fin (A+4))) (hlen : cs.length = origins.length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds advanceReg S (tblRho W (List.replicate W tick) (List.replicate e tick) st))
    (hc : S.R 116 = cs) (hsrc : S.R 109 = origins.flatMap (binSyms W) ++ suffix)
    (hflag : v.flag = cs.head?.isSome) :
    ∃ st' v' S' n, st'.val 2 = w ∧ st'.acc = st.acc ∧ (∀ i, st'.val i < 2^W) ∧
      v'.user = v.user ∧ n ≤ originAdvanceLoopCost W e w previous origins ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          originAdvanceLoopWorkspace W e w previous origins)
        depth (.loop (·.flag) originAdvanceLoopBody) (mk v S) n (mk v' S')) ∧
      tblHolds advanceReg S' (tblRho W (List.replicate W tick) (List.replicate e tick) st') ∧
      S'.R 116 = [] ∧ S'.R 88 = cs.reverse ++ S.R 88 ∧ S'.R 109 = suffix ∧
      S'.R 89 = (origins.flatMap (binSyms W)).reverse ++ S.R 89 ∧
      S'.R 90 = (gatherControls A (originAdvances w previous origins)).reverse ++ S.R 90 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 116 → k ≠ 88 → k ≠ 109 → k ≠ 89 → k ≠ 90 →
        (∀ r, advanceReg r ≠ k) → S'.R k = S.R k := by
  induction origins generalizing previous st cs v S with
  | nil =>
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    refine ⟨st, v, S, 1, hw, rfl, hfit, rfl, by simp [originAdvanceLoopCost, originAdvances],
      (fun depth => ExecWithin.loop_false (by simpa [hnil] using hflag) (by
        unfold originAdvanceLoopWorkspace
        omega)), hS, hc.trans hnil, ?_, ?_, ?_, ?_,
      rfl, rfl, rfl, fun _ _ _ _ _ _ _ => rfl⟩ <;> simp_all [originAdvances, gatherControls]
  | cons origin origins ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      obtain ⟨hprevious, htail⟩ := List.pairwise_cons.mp hsorted
      have hpo := hprevious origin (by simp)
      let S₀ : Stacks 117 A := { S with R := Function.update (Function.update S.R 116 cs) 88 (c::S.R 88) }
      let v₀ : HS 117 Q A U := { v with sym := some c }
      have hpop : (popPush 116 88 : Act 117 Q A U).run (mk v S) = mk v₀ S₀ := by
        simp [popPush, Action.run, update_rt, hc, S₀, v₀]
      have hoff₀ (k : Fin 117) (h116 : k ≠ 116) (h88 : k ≠ 88) : S₀.R k = S.R k := by
        simp [S₀, h116, h88]
      have hb₀ : tblHolds advanceReg S₀ (tblRho W (List.replicate W tick) (List.replicate e tick) st) := by
        intro r
        have hh := advanceReg_range r
        rw [hoff₀ _ (by intro he; rw [he] at hh; omega) (by intro he; rw [he] at hh; omega)]
        exact hS r
      obtain ⟨st₁, v₁, S₁, n₁, ho₁, hp₁, hw₁, hd₁, ha₁, hfit₁, hu₁, hn₁, he₁, hb₁,
        hs₁, hsave₁, hout₁, hi₁, hoFrame₁, hl₁, hf₁⟩ := originAdvanceNext_exec_within (body := body)
        he st hp hw hpo hfit (hcoords origin (by simp))
        ((Nat.mul_le_mul_right w (Nat.sub_le origin previous)).trans_lt (hunits origin (by simp)))
        (origins.flatMap (binSyms W) ++ suffix) v₀ S₀ hb₀
        (by rw [hoff₀ 109 (by decide) (by decide), hsrc]; simp)
      have hhigh (k : Fin 117) (hk : 19 ≤ k.val) : ∀ r, advanceReg r ≠ k := by
        intro r he
        have hh := advanceReg_range r
        rw [he] at hh
        omega
      have hc₁ : S₁.R 116 = cs := by
        rw [hf₁ 116 (by decide) (by decide) (by decide) (hhigh 116 (by decide))]
        simp [S₀]
      have h88₁ : S₁.R 88 = c::S.R 88 := by
        rw [hf₁ 88 (by decide) (by decide) (by decide) (hhigh 88 (by decide))]
        simp [S₀]
      have hpPeek := Exec.act (body := body) (peekR 116) (mk v₁ S₁)
      rw [peekR_run, hc₁] at hpPeek
      obtain ⟨st₂, v₂, S₂, n₂, hw₂, ha₂, hfit₂, hu₂, hn₂, he₂, hb₂, hc₂, h88₂, hs₂, h89₂,
        h90₂, hi₂, ho₂, hl₂, hf₂⟩ := ih htail
        (fun o ho => hcoords o (by simp [ho])) (fun o ho => hunits o (by simp [ho]))
        st₁ hp₁ hw₁ hfit₁ cs (by simpa using hlen)
        { v₁ with flag := cs.head?.isSome } S₁ hb₁ hc₁ hs₁ rfl
      have heBody : Exec body originAdvanceLoopBody (mk v S) (n₁+2)
          (mk { v₁ with flag := cs.head?.isSome } S₁) :=
        (Exec.seq (hpop ▸ Exec.act (body := body) (popPush 116 88) _) (Exec.seq (he₁ 0).toExec hpPeek)).cast (by omega) rfl
      refine ⟨st₂, v₂, S₂, n₁+2+n₂+1, hw₂, ha₂.trans ha₁, hfit₂, hu₂.trans hu₁, ?_,
        ?_, hb₂, hc₂, ?_, hs₂, ?_, ?_,
        hi₂.trans hi₁, ho₂.trans hoFrame₁, hl₂.trans hl₁, ?_⟩
      · simp only [originAdvanceLoopCost, originAdvances, List.length_cons, List.sum_cons] at hn₂ ⊢
        nlinarith only [hn₁, hn₂]
      · intro depth
        have hpopE : Exec body (.act (popPush 116 88)) (mk v S) 1 (mk v₀ S₀) :=
          hpop ▸ Exec.act (body := body) (popPush 116 88) _
        have hpopNative : mnNativePushBound 1
            (.act (popPush (116 : Fin 117) 88) : Pr P 117 Q A U) := by
          simp [popPush,mnNativePushBound,mnActPush]
        have hpeekNative : mnNativePushBound 0
            (.act (peekR (116 : Fin 117)) : Pr P 117 Q A U) := by
          simp [peekR,mnNativePushBound,mnActPush]
        have htpop := mn_native_exec_within hpopE 1 hpopNative depth _ (Nat.le_refl _)
        have htpeek := mn_native_exec_within hpPeek 0 hpeekNative depth _ (Nat.le_refl _)
        have ht := mn_seq_within_add htpop (mn_seq_within_add (he₁ depth) htpeek)
        have htBody := ht.cast (by omega : 1+(n₁+1) = n₁+2) rfl
        have hstock₀ := mn_popPush_size (show (116 : Fin 117) ≠ 88 by decide) c cs v S hc
        change mnSize (mk v₀ S₀) = mnSize (mk v S) at hstock₀
        have hsrc₀ : S₀.R 109 = binSyms W origin++(origins.flatMap (binSyms W)++suffix) := by
          rw [hoff₀ 109 (by decide) (by decide),hsrc]
          simp [List.append_assoc]
        have hstock₁ := originAdvanceNext_stock_le v₀ v₁ S₀ S₁ st st₁ hb₀ hb₁ ha₁
          (origins.flatMap (binSyms W)++suffix) hsrc₀ hs₁ hsave₁ hout₁ hi₁ hoFrame₁ hl₁ hf₁
        have hstock : mnSize (mk {v₁ with flag := cs.head?.isSome} S₁) ≤
            mnSize (mk v S)+(origin-previous)*w+1 := by
          change mnSize (mk v₁ S₁) ≤ _
          omega
        refine ExecWithin.loop_true (by simpa using hflag) (htBody.mono ?_) ((he₂ depth).mono ?_)
        · intro d z hz
          dsimp only [originAdvanceLoopWorkspace,originAdvanceNextWorkspace,originAdvances,
            List.length_cons,List.sum_cons] at *
          omega
        · intro d z hz
          dsimp only [originAdvanceLoopWorkspace,originAdvances,List.length_cons,List.sum_cons] at *
          omega
      · rw [h88₂, h88₁]
        simp [List.reverse_cons, List.append_assoc]
      · rw [h89₂, hsave₁, hoff₀ 89 (by decide) (by decide)]
        simp [List.reverse_append, List.append_assoc]
      · rw [h90₂, hout₁, hoff₀ 90 (by decide) (by decide)]
        simp [originAdvances, gatherControls, List.reverse_append, List.reverse_cons, List.reverse_replicate,
          List.append_assoc]
      · intro k hk116 hk88 hk109 hk89 hk90 hk
        rw [hf₂ k hk116 hk88 hk109 hk89 hk90 hk, hf₁ k hk109 hk89 hk90 hk, hoff₀ k hk116 hk88]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
