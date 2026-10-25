module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpMakeX
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandCounterFrame
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherExec

/-! # Input operand production with generated geometry and complete cleanup -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.Machine
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T} {rg : TblR 10 → Fin T}

noncomputable def chirpMakeXSetup (rg : TblR 10 → Fin T) (cr : CR → Fin T)
    (ι : Fin 64 → Fin T) (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q)
    (batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (chirpOperandCountSetup rg ![batch, rowCount, recordSymbols]) <|
  .seq (chirpMakeX cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
    recordSymbols acc current savedSource saved buf tmp dst) (clearWords [batch, rowCount, recordSymbols])

def chirpMakeXSetupCost (W e t m w : ℕ) : ℕ :=
  let M := chirpBlockCount t m
  let K := M + (3 * m + 1) + (3 * m + 1) * w
  18 * tblC W e + 6 * K + 33 * W + 19 + chirpMakeXCost M m w + 2 * K + 7

/-- Geometry comes from the retained binary dimension bank. Only the X operand destination
changes; every generated counter, intermediate stream, source and scratch tape is restored. -/
theorem chirpMakeXSetup_exec (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hrg : Function.Injective rg)
    {dst batch batchSaved rowCount recordSaved wordR recordSymbols acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, rowCount, recordSaved, wordR, recordSymbols, cr .out,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (hbank : ∀ i b, rg b ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hcounter : ∀ i r, cr r ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    (hss : ∀ i j, ι j ≠ (![batch, rowCount, recordSymbols] : Fin 3 → Fin T) i)
    {W e s t α q w m : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (htval : st.val 1 = t) (hmval : st.val 2 = m) (hwval : st.val 3 = w)
    (hs : 0 < s) (ht : 0 < t) (hm : 0 < m) (hα : 0 < α) (hq : 13 ≤ q) (hw : q + 3 ≤ w)
    (hsize : 3 * m + 1 < 2 ^ W) (hvolume : (3 * m + 1) * w < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (ρ : CR → List (Fin (A + 4))) (hr : Ready ρ w q)
    (hX : ρ .xs = cstream A w ((List.range (chirpBlockCount t m)).flatMap fun n => chirpWindow s t m n u))
    (hY : ρ .ys = chirpBlockStream (chirpBlockCount t m) (fun n => chirpEntryStream A w (3 * m + 1)
      (fun a => chirpNegativeNumerator false s t α q m (n * m) a)))
    (hxsv : ρ .xsv = []) (hysv : ρ .ysv = []) (hacc : ρ .acc = []) (hout : ρ .out = [])
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S) (hS : CHolds cr S ρ)
    (hb : tblHolds rg S (tblRho W wl nl st)) (hword : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [batch, rowCount, recordSymbols, batchSaved, acc, savedSource, recordSaved,
      current, saved, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpMakeXSetupCost W e t m w ∧
      Exec body (chirpMakeXSetup rg cr ι hι hT hQ batch batchSaved rowCount recordSaved wordR
        recordSymbols acc current savedSource saved buf tmp dst) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w ((List.range (chirpBlockCount t m)).flatMap fun n =>
            chirpOperandX s t q m n (chirpInputNumerators s t α q m) u) ++ S.R dst)) }) := by
  let counters : Fin 3 → Fin T := ![batch, rowCount, recordSymbols]
  have hcnd : [batch, rowCount, recordSymbols].Nodup := by
    have hreg' := hreg
    regs_ne hreg'
    simp_all
  have hcinj : Function.Injective counters := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [counters, List.nodup_cons]
  have hblank (i : Fin 3) : S.R (counters i) = [] := by
    fin_cases i <;> exact hclean _ (by simp [counters])
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpOperandCountSetup_exec (body := body) hrg counters
    hbank wl nl hwl hnl heW st t m w htval hmval hwval ht hm hsize hvolume hzero hfit v S hb
  let S₁ : Stacks T A := { S with R := (unaryCopiesR (chirpOperandCountValues t m w) S.R
    (chirpOperandAssignments counters)) }
  have off (k : Fin T) (hk : ∀ i, k ≠ counters i) : S₁.R k = S.R k :=
    chirpOperandCounters_off counters t m w S.R k hk
  have hat (i : Fin 3) : S₁.R (counters i) = List.replicate (chirpOperandCount t m w i) tick := by
    simpa only [hblank, List.append_nil] using
      chirpOperandCounters_at counters hcinj t m w S.R i
  have hS₁ : CHolds cr S₁ ρ := fun r => (off _ (fun i => hcounter i r)).trans (hS r)
  have hc₁ : CClean ι S₁ := fun j => ⟨(hc j).1, (off _ (fun i => hss i j)).trans (hc j).2⟩
  have hreg' := hreg
  regs_ne hreg'
  have hoff (k : Fin T) (hb' : k ≠ batch) (hr' : k ≠ rowCount) (hv' : k ≠ recordSymbols) :
      S₁.R k = S.R k := by
    apply off
    intro i
    fin_cases i <;> assumption
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpMakeX_exec (body := body) (M := chirpBlockCount t m) hcr hdisj hι hT hQ hA hreg
    hs ht hα hq hw (fun n hn => chirpBlock_valid ht hm hn) u hu ρ hr hX hY hxsv hysv hacc hout
    v₁ S₁ hc₁ hS₁
    (by simpa [counters, chirpOperandCount] using congrArg List.length (hat 0))
    (by simpa [counters, chirpOperandCount] using congrArg List.length (hat 1))
    (by rw [hoff _ ‹batch ≠ wordR›.symm ‹rowCount ≠ wordR›.symm ‹wordR ≠ recordSymbols›]; exact hword)
    (by simpa [counters, chirpOperandCount] using congrArg List.length (hat 2))
    (by
      intro k hk
      have hc' := hclean k (List.mem_append_right [batch, rowCount, recordSymbols] hk)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hoff _ (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))
          (by first | assumption | (apply Ne.symm; assumption))] <;> exact hc')
  let words := cstream A w ((List.range (chirpBlockCount t m)).flatMap fun n =>
    chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (words ++ S₁.R dst) }
  have hat₂ (i : Fin 3) : S₂.R (counters i) = List.replicate (chirpOperandCount t m w i) tick := by
    change Function.update S₁.R dst _ (counters i) = _
    rw [Function.update_of_ne (by fin_cases i <;> first | assumption | (apply Ne.symm; assumption))]
    exact hat i
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [batch, rowCount, recordSymbols] hcnd v₂ S₂
  have hcost : (List.map (fun k => (S₂.R k).length) [batch, rowCount, recordSymbols]).sum =
      chirpBlockCount t m + (3 * m + 1) + (3 * m + 1) * w := by
    have h0 := congrArg List.length (hat₂ 0)
    have h1 := congrArg List.length (hat₂ 1)
    have h2 := congrArg List.length (hat₂ 2)
    simp [counters, chirpOperandCount] at h0 h1 h2
    simp [h0, h1, h2, Nat.add_assoc]
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), ?_, (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hcost]
    simp only [List.length_cons, List.length_nil]
    dsimp only [chirpMakeXSetupCost]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃
    funext k
    by_cases hk : k ∈ [batch, rowCount, recordSymbols]
    · have hkdst : k ≠ dst := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact Ne.symm (by assumption)
      have hkblank := hclean k (List.mem_append_left _ hk)
      simp only [ite_eq_left hk, Function.update_of_ne hkdst, hkblank]
    · have hk' : ∀ i, k ≠ counters i := by
        intro i
        have hn : k ≠ batch ∧ k ≠ rowCount ∧ k ≠ recordSymbols := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hk
        fin_cases i
        · exact hn.1
        · exact hn.2.1
        · exact hn.2.2
      have hdst : S₁.R dst = S.R dst := hoff _ ‹dst ≠ batch› ‹dst ≠ rowCount› ‹dst ≠ recordSymbols›
      simp only [ite_eq_right hk, S₂, hdst]
      by_cases hd : k = dst
      · subst k; simp only [Function.update_self]; rfl
      · simp only [Function.update_of_ne hd, off k hk']

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
