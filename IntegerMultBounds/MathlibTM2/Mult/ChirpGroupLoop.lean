module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupStep

/-! # The counted forward-line loop with one retained setup -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def groupLineInput (A s α p : ℕ) (u : ZMod s → GaussianInt) : List (Fin (A + 4)) :=
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  cstream A (q + l + Γ + 5) (chirpLine s u)

noncomputable def groupLineOutput (A s t α p : ℕ) (u : ZMod s → GaussianInt) : List (Fin (A + 4)) :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  cstream A (p + l + Γ + 5) (chirpForwardOutput s t α p q l Γ m u)

noncomputable def groupLineCost (A s t α p : ℕ) (u : ZMod s → GaussianInt) (shared : Bool := false) : ℕ :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  chirpRawCorrelationModeCost shared W w W w s t q l m w +
    chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t +
    16 * (groupLineInput A s α p u).length + 2 * (groupLineOutput A s t α p u).length + 18

noncomputable def groupLoopBody (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (shared : Bool := false) : Pr P 640 Q A U :=
  .seq (.act (popPush lineCount savedLineCount))
    (.seq (groupStep hQ hQrp shared) (.act (peekR lineCount)))

def groupLoopR (cs xs rest ys : List (Fin (A + 4))) (R : Regs 640 A) : Regs 640 A :=
  groupStepR xs rest ys (Function.update (Function.update R lineCount [])
    savedLineCount (cs.reverse ++ R savedLineCount))

private theorem groupLoopR_cons (c : Fin (A + 4))
    (cs xs xs' ys ys' rest : List (Fin (A + 4))) (R : Regs 640 A) :
    groupLoopR cs xs' rest ys' (groupStepR xs (xs' ++ rest) ys
      (Function.update (Function.update R lineCount cs) savedLineCount (c :: R savedLineCount))) =
    groupLoopR (c :: cs) (xs ++ xs') rest (ys ++ ys') R := by
  have hreg : [lineCount, savedLineCount, groupInput, inputArchive, outputArchive].Nodup := by decide +kernel
  regs_ne hreg
  funext k
  by_cases hn : k = lineCount
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases hs : k = savedLineCount
  · subst k; simp_all [groupLoopR, groupStepR, List.append_assoc]
  by_cases hi : k = groupInput
  · subst k; simp_all [groupLoopR, groupStepR]
  by_cases ha : k = inputArchive
  · subst k; simp_all [groupLoopR, groupStepR, List.reverse_append, List.append_assoc]
  by_cases ho : k = outputArchive
  · subst k; simp_all [groupLoopR, groupStepR, List.reverse_append, List.append_assoc]
  · simp_all [groupLoopR, groupStepR]

/-- The loop executes each supplied mathematical line using the actual fixed forward program. -/
theorem groupLoop_exec {shared : Bool} (hQ : SS.states ≤ Q) (hQrp : rpStates ≤ Q) (hA : 96 ≤ A)
    (s t α p : ℕ) [NeZero s] [NeZero t] (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p)
    (us : List (ZMod s → GaussianInt))
    (hu : ∀ u ∈ us, ∀ j,
      ‖value (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α)) (u j)‖ ≤ 1)
    (cs : List (Fin (A + 4))) (hcs : cs.length = us.length)
    (v : HS 640 Q A U) (S : Stacks 640 A) (rest : List (Fin (A + 4)))
    (hd : SelectedLineData s t α p S shared) (hc : S.R lineCount = cs)
    (hi : S.R groupInput = (us.map (groupLineInput A s α p)).flatten ++ rest)
    (hw : (S.R lineSymbols).length =
      s * (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
        chirpForwardRingLog p α + chirpForwardGrowth p + 5))
    (hr : S.R (raw .raw) = []) (hb : S.R groupBuf = []) (ht : S.R groupTmp = [])
    (hf : v.flag = cs.head?.isSome) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (us.map (fun u => groupLineCost A s t α p u shared)).sum + 3 * us.length + 1 ∧
      Exec body (.loop (·.flag) (groupLoopBody hQ hQrp shared)) (mk v S) n
        (mk v' { S with R := (groupLoopR cs
          (us.map (groupLineInput A s α p)).flatten rest
          (us.map (groupLineOutput A s t α p)).flatten S.R) }) := by
  have hreg : [lineCount, savedLineCount, groupInput, inputArchive, outputArchive,
      lineSymbols, groupBuf, groupTmp, raw .raw].Nodup := by decide +kernel
  regs_ne hreg
  induction us generalizing cs v S with
  | nil =>
      have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcs)
      simp only [hnil] at hc hf ⊢
      refine ⟨v, 1, rfl, by simp, ?_⟩
      have he := Exec.loop_false (body := body) (p := groupLoopBody hQ hQrp shared)
        (show v.flag = false by simpa using hf) (s := mk v S)
      convert he using 1
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      simp only [List.map_nil, List.flatten_nil, groupLoopR, groupStepR,
        List.reverse_nil, List.nil_append, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | cons u us ih =>
      cases cs with
      | nil => simp at hcs
      | cons c cs =>
        let S₀ : Stacks 640 A := { S with R := (Function.update
          (Function.update S.R lineCount cs) savedLineCount (c :: S.R savedLineCount)) }
        have hrun : (popPush lineCount savedLineCount : Act 640 Q A U).run (mk v S) =
            mk { v with sym := some c } S₀ := by
          simp [popPush, Action.run, hc, update_rt, S₀, (‹lineCount ≠ savedLineCount›.symm)]
        have hlow : ∀ k, k.val < 533 → S₀.R k = S.R k := by
          intro k hk
          have hn : k ≠ lineCount := by
            intro he; have hv := congrArg Fin.val he; change k.val = 544 at hv; omega
          have hs : k ≠ savedLineCount := by
            intro he; have hv := congrArg Fin.val he; change k.val = 545 at hv; omega
          simp only [S₀, Function.update_of_ne hs, Function.update_of_ne hn]
        have hd₀ : SelectedLineData s t α p S₀ shared :=
          hd.frame (S' := S₀) rfl (fun k hk => hlow k hk.1)
        let xs := groupLineInput A s α p u
        let ys := groupLineOutput A s t α p u
        let tail := (us.map (groupLineInput A s α p)).flatten ++ rest
        obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := groupStep_exec (shared := shared) (body := body)
          hQ hQrp hA s t α p hst hα hαp u (hu u (by simp))
          { v with sym := some c } S₀ tail hd₀
          (by simpa [S₀, tail, groupLineInput, List.flatten_cons, List.append_assoc,
            (‹lineCount ≠ groupInput›.symm), (‹savedLineCount ≠ groupInput›.symm)] using hi)
          (by simpa [S₀, groupLineInput, length_cstream, length_chirpLine,
            (‹lineCount ≠ lineSymbols›.symm), (‹savedLineCount ≠ lineSymbols›.symm)] using hw)
          (by simpa [S₀, (‹lineCount ≠ raw .raw›.symm), (‹savedLineCount ≠ raw .raw›.symm)] using hr)
          (by simpa [S₀, (‹lineCount ≠ groupBuf›.symm), (‹savedLineCount ≠ groupBuf›.symm)] using hb)
          (by simpa [S₀, (‹lineCount ≠ groupTmp›.symm), (‹savedLineCount ≠ groupTmp›.symm)] using ht)
        let S₁ : Stacks 640 A := { S₀ with R := groupStepR xs tail ys S₀.R }
        have e (k : Fin 640) (hi : k ≠ groupInput) (ha : k ≠ inputArchive)
            (ho : k ≠ outputArchive) : S₁.R k = S₀.R k := by
          simp only [S₁, groupStepR, Function.update_of_ne ho, Function.update_of_ne ha,
            Function.update_of_ne hi]
        have hd₁ : SelectedLineData s t α p S₁ shared := hd₀.groupStep xs tail ys
        obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := ih
          (fun z hz => hu z (by simp [hz])) cs (by simpa using hcs)
          { v₁ with flag := (S₁.R lineCount).head?.isSome } S₁ hd₁
          (by simp [(e _ ‹lineCount ≠ groupInput› ‹lineCount ≠ inputArchive›
            ‹lineCount ≠ outputArchive›), S₀, ‹lineCount ≠ savedLineCount›])
          (by simp [S₁, groupStepR, tail, ‹groupInput ≠ outputArchive›, ‹groupInput ≠ inputArchive›])
          (by simpa [(e _ (‹groupInput ≠ lineSymbols›.symm) (‹inputArchive ≠ lineSymbols›.symm)
            (‹outputArchive ≠ lineSymbols›.symm)), S₀, (‹lineCount ≠ lineSymbols›.symm),
            (‹savedLineCount ≠ lineSymbols›.symm)] using hw)
          (by simpa [S₁, groupStepR_low xs tail ys S₀.R (raw .raw) (by decide +kernel),
            S₀, (‹lineCount ≠ raw .raw›.symm), (‹savedLineCount ≠ raw .raw›.symm)] using hr)
          (by simpa [(e _ (‹groupInput ≠ groupBuf›.symm) (‹inputArchive ≠ groupBuf›.symm)
            (‹outputArchive ≠ groupBuf›.symm)), S₀, (‹lineCount ≠ groupBuf›.symm),
            (‹savedLineCount ≠ groupBuf›.symm)] using hb)
          (by simpa [(e _ (‹groupInput ≠ groupTmp›.symm) (‹inputArchive ≠ groupTmp›.symm)
            (‹outputArchive ≠ groupTmp›.symm)), S₀, (‹lineCount ≠ groupTmp›.symm),
            (‹savedLineCount ≠ groupTmp›.symm)] using ht)
          (by simp [(e _ ‹lineCount ≠ groupInput› ‹lineCount ≠ inputArchive›
            ‹lineCount ≠ outputArchive›), S₀, ‹lineCount ≠ savedLineCount›])
        have hp := Exec.act (body := body) (peekR lineCount) (mk v₁ S₁)
        rw [peekR_run] at hp
        refine ⟨v₂, 1 + (1 + (n₁ + 1)) + n₂, hu₂.trans hu₁, ?_, ?_⟩
        · change n₁ ≤ groupLineCost A s t α p u shared at hn₁
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          omega
        · have he := Exec.loop_true (by simpa using hf)
            (Exec.seq (hrun ▸ Exec.act (body := body) (popPush lineCount savedLineCount) (mk v S))
              (Exec.seq he₁ hp)) he₂
          refine he.cast (by omega) ?_
          congr 1
          ext1
          · rfl
          · rfl
          · rfl
          change groupLoopR cs (us.map (groupLineInput A s α p)).flatten rest
            (us.map (groupLineOutput A s t α p)).flatten S₁.R = _
          simpa only [S₁, S₀, tail, List.map_cons, List.flatten_cons] using
            groupLoopR_cons c cs xs (us.map (groupLineInput A s α p)).flatten ys
              (us.map (groupLineOutput A s t α p)).flatten rest S.R


end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
