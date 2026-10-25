module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpExtract
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvBatchPacking

/-! # Extract arbitrary slices from one shared ring-product stream

Each record is selected in chirp output order. The accumulator reverses whole symbol
streams, so one final move restores both block order and the low-bit-first words.
The source and all reusable counters and scratch are restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Extract one record into a reversed-symbol accumulator, saving the consumed source. -/
def correlationNext
    (skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (reverseSlice skip savedSkip mR recordSaved wordR src current saved buf tmp) <|
  .seq (moveR current acc id) (transfer recordSymbols src savedSource tmp)

/-- One shared-counter extraction step, with arbitrary accumulator and source tails. -/
theorem sliceNext_exec
    {skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src, acc, current,
      savedSource, saved, buf, tmp].Nodup)
    (w a m r : ℕ) (xs : List GaussianInt) (hlen : xs.length = r) (hsize : a + m ≤ r)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w xs ++ tail)
    (hskip : (S.R skip).length = a * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hcurrent : S.R current = []) (hsaved : S.R saved = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (correlationNext skip savedSkip mR recordSaved wordR recordSymbols src acc
        current savedSource saved buf tmp) (mk v S) (6 * a * w + 18 * m * w + 19 * m + 4 * r * w + 18)
        (mk v' { S with R := (Function.update
          (Function.update (Function.update S.R src tail) savedSource
            ((cstream A w xs).reverse ++ S.R savedSource)) acc
            ((cstream A w (sliceCoeffs a m xs)).reverse ++ S.R acc)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := sliceCoeffs_exec (body := body)
    (show [skip, savedSkip, mR, recordSaved, wordR, src, current, saved, buf, tmp].Nodup by
      simp_all) w a m xs (by omega) v S tail hsrc hskip hm hw
    hsavedSkip hrecordSaved hsaved hbuf htmp
  set S₁ : Stacks T A := { S with R := (Function.update S.R current
    (cstream A w (sliceCoeffs a m xs) ++ S.R current)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body current acc ‹acc ≠ current›.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R current acc id (S₁.R current) }
  have e (k : Fin T) (hc : k ≠ current) (ha : k ≠ acc) : S₂.R k = S.R k := by
    simp [S₂, S₁, movedR, hc, ha]
  obtain ⟨v₃, hu₃, he₃⟩ := transfer_exec (body := body)
    (show [recordSymbols, src, savedSource, tmp].Nodup by simp_all)
    v₂ S₂ (cstream A w xs) tail
    (by rw [e _ ‹src ≠ current› ‹src ≠ acc›]; exact hsrc)
    (by rw [e _ ‹recordSymbols ≠ current› ‹recordSymbols ≠ acc›, length_cstream, hlen]; exact hrecord)
    (by rw [e _ ‹current ≠ tmp›.symm ‹acc ≠ tmp›.symm]; exact htmp)
  have hcorr : (sliceCoeffs a m xs).length = m := by
    simp only [sliceCoeffs, List.length_reverse, List.length_take, List.length_drop, hlen]
    omega
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp only [S₁, Function.update_self, hcurrent, List.append_nil, length_cstream, hcorr, hlen]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hu₁ hu₂ hu₃ e
    funext k
    simp (disch := first | assumption | (apply Ne.symm; assumption)) only
      [S₂, S₁, movedR, Function.update_self, Function.update_of_ne, List.map_id,
        hcurrent, List.append_nil]
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

theorem correlationNext_exec
    {skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src, acc, current,
      savedSource, saved, buf, tmp].Nodup)
    (w m r : ℕ) (xs : List GaussianInt) (hlen : xs.length = r) (hsize : 4 * m ≤ r)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hsrc : S.R src = cstream A w xs ++ tail)
    (hskip : (S.R skip).length = 3 * m * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hsavedSkip : S.R savedSkip = []) (hrecordSaved : S.R recordSaved = [])
    (hcurrent : S.R current = []) (hsaved : S.R saved = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (correlationNext skip savedSkip mR recordSaved wordR recordSymbols src acc
        current savedSource saved buf tmp) (mk v S) (36 * m * w + 19 * m + 4 * r * w + 18)
        (mk v' { S with R := (Function.update
          (Function.update (Function.update S.R src tail) savedSource
            ((cstream A w xs).reverse ++ S.R savedSource)) acc
            ((cstream A w (correlationCoeffs m xs)).reverse ++ S.R acc)) }) := by
  have h := sliceNext_exec (body := body) hreg w (3 * m) m r xs hlen (by omega)
    v S tail hsrc hskip hm hw hrecord hsavedSkip hrecordSaved hcurrent hsaved hbuf htmp
  simpa only [sliceCoeffs_chirp,
    show 6 * (3 * m) * w + 18 * m * w = 36 * m * w by ring] using h

/-- Consume one batch count symbol and extract the next product record. -/
def correlationLoopBody
    (batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (.act (popPush batch batchSaved))
    (.seq (correlationNext skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp)
      (.act (peekR batch)))

/-- Shared-counter loop invariant, proved structurally over the actual product records. -/
theorem sliceLoop_exec
    {batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w a m r : ℕ) (hsize : a + m ≤ r) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r)
    (cs : List (Fin (A + 4))) (hcs : cs.length = blocks.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : S.R batch = cs) (hsrc : S.R src = cstream A w blocks.flatten ++ tail)
    (hskip : (S.R skip).length = a * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [savedSkip, recordSaved, current, saved, buf, tmp], S.R k = [])
    (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (correlationLoopBody batch batchSaved skip savedSkip mR
        recordSaved wordR recordSymbols src acc current savedSource saved buf tmp))
        (mk v S) (blocks.length * (6 * a * w + 18 * m * w + 19 * m + 4 * r * w + 21) + 1)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R batch []) batchSaved
            (cs.reverse ++ S.R batchSaved)) src tail) savedSource
            ((cstream A w blocks.flatten).reverse ++ S.R savedSource)) acc
            ((cstream A w (blocks.flatMap (sliceCoeffs a m))).reverse ++ S.R acc)) }) := by
  have hnext : [skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src, acc, current,
      savedSource, saved, buf, tmp].Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hreg).2).2
  have hreg' := hreg
  regs_ne hreg'
  induction blocks generalizing cs v S with
  | nil =>
      have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcs)
      simp only [hnil] at hbatch hflag ⊢
      refine ⟨v, rfl, ?_⟩
      have he := Exec.loop_false (body := body)
        (p := correlationLoopBody batch batchSaved skip savedSkip mR recordSaved wordR
          recordSymbols src acc current savedSource saved buf tmp)
        (show v.flag = false by simpa using hflag) (s := mk v S)
      convert he using 1 <;> simp only [List.length_nil, Nat.zero_mul, Nat.zero_add,
        List.flatten_nil, List.flatMap_nil, cstream_nil, List.reverse_nil, List.nil_append]
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | cons xs blocks ih =>
      cases cs with
      | nil => simp at hcs
      | cons c cs =>
          set S₀ : Stacks T A := { S with R := (Function.update (Function.update S.R batch cs)
            batchSaved (c :: S.R batchSaved)) }
          have hrun : (popPush batch batchSaved : Act T Q A U).run (mk v S) =
              mk { v with sym := some c } S₀ := by
            simp [popPush, Action.run, hbatch, update_rt, S₀, ‹batch ≠ batchSaved›.symm]
          have off₀ (k : Fin T) (hb : k ≠ batch) (hs : k ≠ batchSaved) : S₀.R k = S.R k := by
            simp [S₀, hb, hs]
          have clean₀ : ∀ k ∈ [savedSkip, recordSaved, current, saved, buf, tmp], S₀.R k = [] := by
            intro k hk
            have hc := hclean k hk
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
              rw [off₀ _ (by first | assumption | (apply Ne.symm; assumption))
                (by first | assumption | (apply Ne.symm; assumption))] <;> exact hc
          obtain ⟨v₁, hu₁, he₁⟩ := sliceNext_exec (body := body)
            hnext w a m r xs (hlen xs (by simp)) hsize { v with sym := some c } S₀
            (cstream A w blocks.flatten ++ tail)
            (by simpa [off₀ _ ‹batch ≠ src›.symm ‹batchSaved ≠ src›.symm,
              List.flatten_cons, cstream_append, List.append_assoc] using hsrc)
            (by simpa [off₀ _ ‹batch ≠ skip›.symm ‹batchSaved ≠ skip›.symm] using hskip)
            (by simpa [off₀ _ ‹batch ≠ mR›.symm ‹batchSaved ≠ mR›.symm] using hm)
            (by simpa [off₀ _ ‹batch ≠ wordR›.symm ‹batchSaved ≠ wordR›.symm] using hw)
            (by simpa [off₀ _ ‹batch ≠ recordSymbols›.symm ‹batchSaved ≠ recordSymbols›.symm] using hrecord)
            (clean₀ _ (by simp)) (clean₀ _ (by simp)) (clean₀ _ (by simp))
            (clean₀ _ (by simp)) (clean₀ _ (by simp)) (clean₀ _ (by simp))
          set S₁ : Stacks T A := { S₀ with R := (Function.update (Function.update
            (Function.update S₀.R src (cstream A w blocks.flatten ++ tail)) savedSource
              ((cstream A w xs).reverse ++ S₀.R savedSource)) acc
              ((cstream A w (sliceCoeffs a m xs)).reverse ++ S₀.R acc)) }
          have off₁ (k : Fin T) (hs : k ≠ src) (hv : k ≠ savedSource) (ha : k ≠ acc) :
              S₁.R k = S₀.R k := by simp [S₁, hs, hv, ha]
          have stable : ∀ k ∈ [skip, savedSkip, mR, recordSaved, wordR, recordSymbols, current, saved, buf, tmp],
              S₁.R k = S.R k := by
            intro k hk
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              rw [off₁ _ (by first | assumption | (apply Ne.symm; assumption))
                (by first | assumption | (apply Ne.symm; assumption))
                (by first | assumption | (apply Ne.symm; assumption)),
                off₀ _ (by first | assumption | (apply Ne.symm; assumption))
                (by first | assumption | (apply Ne.symm; assumption))]
          obtain ⟨v₂, hu₂, he₂⟩ := ih (fun ys hy => hlen ys (by simp [hy])) cs
            (by simpa using hcs) { v₁ with flag := (S₁.R batch).head?.isSome } S₁
            (by simp [off₁ _ ‹batch ≠ src› ‹batch ≠ savedSource› ‹batch ≠ acc›, S₀, ‹batch ≠ batchSaved›])
            (by simp [S₁, ‹src ≠ acc›, ‹src ≠ savedSource›])
            (by rw [stable _ (by simp)]; exact hskip)
            (by rw [stable _ (by simp)]; exact hm)
            (by rw [stable _ (by simp)]; exact hw)
            (by rw [stable _ (by simp)]; exact hrecord)
            (by
              intro k hk
              have hc := hclean k hk
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
              rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
                rw [stable _ (by simp)] <;> exact hc)
            (by simp [off₁ _ ‹batch ≠ src› ‹batch ≠ savedSource› ‹batch ≠ acc›, S₀, ‹batch ≠ batchSaved›])
          have hpeek := Exec.act (body := body) (peekR batch) (mk v₁ S₁)
          rw [peekR_run] at hpeek
          refine ⟨v₂, hu₂.trans hu₁, (Exec.loop_true (by simpa using hflag)
            (Exec.seq (hrun ▸ Exec.act (body := body) (popPush batch batchSaved) (mk v S))
              (Exec.seq he₁ hpeek)) he₂).cast ?_ ?_⟩
          · simp only [List.length_cons]
            ring
          · congr 1
            ext1
            · rfl
            · rfl
            · rfl
            clear he₁ he₂ hpeek hrun hu₁ hu₂ ih hlen hcs hflag hbatch hsrc hskip hm hw hrecord
              hclean clean₀ off₀ off₁ stable
            funext k
            by_cases hk0 : k = batch
            · subst k
              simp (disch := first | assumption | (apply Ne.symm; assumption)) only
                [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                  List.flatMap_cons, cstream_append, List.reverse_append, List.reverse_cons,
                  List.append_assoc, List.cons_append, List.nil_append]
            by_cases hk1 : k = batchSaved
            · subst k
              simp (disch := first | assumption | (apply Ne.symm; assumption)) only
                [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                  List.flatMap_cons, cstream_append, List.reverse_append, List.reverse_cons,
                  List.append_assoc, List.cons_append, List.nil_append]
            by_cases hk2 : k = src
            · subst k
              simp (disch := first | assumption | (apply Ne.symm; assumption)) only
                [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                  List.flatMap_cons, cstream_append, List.reverse_append, List.reverse_cons,
                  List.append_assoc, List.cons_append, List.nil_append]
            by_cases hk3 : k = savedSource
            · subst k
              simp (disch := first | assumption | (apply Ne.symm; assumption)) only
                [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                  List.flatMap_cons, cstream_append, List.reverse_append, List.reverse_cons,
                  List.append_assoc, List.cons_append, List.nil_append]
            by_cases hk4 : k = acc
            · subst k
              simp (disch := first | assumption | (apply Ne.symm; assumption)) only
                [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                  List.flatMap_cons, cstream_append, List.reverse_append, List.reverse_cons,
                  List.append_assoc, List.cons_append, List.nil_append]
            ·
              simp (disch := first | assumption | (apply Ne.symm; assumption)) only
                [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                  List.flatMap_cons, cstream_append, List.reverse_append, List.reverse_cons,
                  List.append_assoc, List.cons_append, List.nil_append]
theorem correlationLoop_exec
    {batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    (w m r : ℕ) (hsize : 4 * m ≤ r) (blocks : List (List GaussianInt))
    (hlen : ∀ xs ∈ blocks, xs.length = r)
    (cs : List (Fin (A + 4))) (hcs : cs.length = blocks.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : S.R batch = cs) (hsrc : S.R src = cstream A w blocks.flatten ++ tail)
    (hskip : (S.R skip).length = 3 * m * w) (hm : (S.R mR).length = m)
    (hw : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = r * w)
    (hclean : ∀ k ∈ [savedSkip, recordSaved, current, saved, buf, tmp], S.R k = [])
    (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (correlationLoopBody batch batchSaved skip savedSkip mR
        recordSaved wordR recordSymbols src acc current savedSource saved buf tmp))
        (mk v S) (blocks.length * (36 * m * w + 19 * m + 4 * r * w + 21) + 1)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R batch []) batchSaved
            (cs.reverse ++ S.R batchSaved)) src tail) savedSource
            ((cstream A w blocks.flatten).reverse ++ S.R savedSource)) acc
            ((cstream A w (blocks.flatMap (correlationCoeffs m))).reverse ++ S.R acc)) }) := by
  have h := sliceLoop_exec (body := body) hreg w (3 * m) m r (by omega) blocks hlen cs hcs
    v S tail hbatch hsrc hskip hm hw hrecord hclean hflag
  simpa only [sliceCoeffs_chirp,
    show 6 * (3 * m) * w + 18 * m * w = 36 * m * w by ring] using h


end IntegerMultBounds.MathlibTM2.Mult.ShortConv
