module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Pack a stream of equally sized short-convolution blocks

The input contains consecutive raw blocks. A reusable symbol-count counter selects one block;
a reusable padding counter supplies its zero suffix. The loop saves and restores the complete
raw stream, and produces padded records in their original order. It runs on a fixed tape bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Copy one raw block to a buffer, save its consumed original, append its reversed symbols
and zero padding to the accumulator. The buffer and per-block copy workspace end empty. -/
def packNext (count pad src saved acc buf savedBlock tmp : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix count src buf savedBlock tmp) <|
  .seq (transfer count src saved tmp) <|
  .seq (moveR buf acc id) (umulSym 1 (pairSym A false false) pad acc tmp)

/-- One packing step, including both copies and padding. Saved input and accumulator tails
may already contain earlier blocks. -/
theorem packNext_exec {count pad src saved acc buf savedBlock tmp : Fin T}
    (hreg : [count, pad, src, saved, acc, buf, savedBlock, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs rest : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ rest) (hlen : (S.R count).length = xs.length)
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packNext count pad src saved acc buf savedBlock tmp) (mk v S)
        (16 * xs.length + 4 * (S.R pad).length + 20)
        (mk v' { S with R := (Function.update
          (Function.update (Function.update S.R src rest) saved (xs.reverse ++ S.R saved))
          acc (List.replicate (S.R pad).length (pairSym A false false) ++ xs.reverse ++ S.R acc)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyPrefix_exec (body := body)
    (show [count, src, buf, savedBlock, tmp].Nodup by simp_all) v S xs rest hsrc hlen hsavedBlock htmp
  set S₁ : Stacks T A := { S with R := Function.update S.R buf (xs ++ S.R buf) }
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body)
    (show [count, src, saved, tmp].Nodup by simp_all) v₁ S₁ xs rest
    (by simpa [S₁, ‹src ≠ buf›] using hsrc)
    (by simpa [S₁, ‹count ≠ buf›] using hlen)
    (by simp [S₁, ‹buf ≠ tmp›.symm, htmp])
  set S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src rest) saved
    (xs.reverse ++ S₁.R saved)) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body buf acc ‹acc ≠ buf›.symm id v₂ S₂
  set S₃ : Stacks T A := { S₂ with R := movedR S₂.R buf acc id (S₂.R buf) }
  obtain ⟨v₄, hu₄, he₄⟩ := umulSym_exec body 1 (pairSym A false false)
    ‹pad ≠ acc› ‹pad ≠ tmp› ‹acc ≠ tmp› v₃ S₃
    (by simp [S₃, S₂, S₁, movedR, ‹buf ≠ tmp›.symm, ‹acc ≠ tmp›.symm,
      ‹src ≠ tmp›.symm, ‹saved ≠ tmp›.symm, htmp])
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₃, S₂, S₁, movedR, ‹saved ≠ buf›.symm, ‹src ≠ buf›.symm,
      ‹pad ≠ acc›, ‹pad ≠ buf›, ‹pad ≠ src›, ‹pad ≠ saved›, hbuf]
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext r
    simp only [S₃, S₂, S₁, movedR, Function.update_apply, List.map_id, hbuf,
      List.append_nil, one_mul]
    split_ifs <;> subst_vars <;> simp_all [List.append_assoc]

/-- Loop body: consume one record-count symbol, pack one block, test the count again. -/
def packLoopBody (records recordSaved count pad src saved acc buf savedBlock tmp : Fin T) :
    Pr P T Q A U :=
  .seq (.act (popPush records recordSaved))
    (.seq (packNext count pad src saved acc buf savedBlock tmp) (.act (peekR records)))

/-- Packing loop before final restoration. Its proof follows the block list structurally;
there is no generated execution certificate or per-record setup oracle. -/
theorem packLoop_prefix_exec {records recordSaved count pad src saved acc buf savedBlock tmp : Fin T}
    (hreg : [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp].Nodup)
    (a : ℕ) (blocks : List (List (Fin (A + 4)))) (hlen : ∀ xs ∈ blocks, xs.length = a)
    (cs : List (Fin (A + 4))) (hcs : cs.length = blocks.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hrecords : S.R records = cs) (hsrc : S.R src = blocks.flatten ++ tail)
    (hcount : (S.R count).length = a)
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = [])
    (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (packLoopBody records recordSaved count pad src saved acc buf savedBlock tmp))
        (mk v S) (blocks.length * (16 * a + 4 * (S.R pad).length + 23) + 1)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R records []) recordSaved
            (cs.reverse ++ S.R recordSaved)) src tail) saved
            (blocks.flatten.reverse ++ S.R saved)) acc
            ((blocks.flatMap fun xs => xs ++ List.replicate (S.R pad).length
              (pairSym A false false)).reverse ++ S.R acc)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  induction blocks generalizing cs v S with
  | nil =>
      have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcs)
      simp only [hnil] at hrecords hflag ⊢
      refine ⟨v, rfl, ?_⟩
      have he := Exec.loop_false (body := body)
        (p := packLoopBody records recordSaved count pad src saved acc buf savedBlock tmp)
        (show v.flag = false by simpa using hflag) (s := mk v S)
      convert he using 1 <;> simp only [List.length_nil, Nat.zero_mul, Nat.zero_add,
        List.flatten_nil, List.flatMap_nil, List.reverse_nil, List.nil_append]
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext r
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | cons xs blocks ih =>
      cases cs with
      | nil => simp at hcs
      | cons c cs =>
          have hxs : xs.length = a := hlen xs (by simp)
          have hlen' : ∀ ys ∈ blocks, ys.length = a := fun ys hy => hlen ys (by simp [hy])
          have hcs' : cs.length = blocks.length := by simpa using hcs
          set S₀ : Stacks T A := { S with R := (Function.update (Function.update S.R records cs)
            recordSaved (c :: S.R recordSaved)) }
          have hrun : (popPush records recordSaved : Act T Q A U).run (mk v S) =
              mk { v with sym := some c } S₀ := by
            simp [popPush, Action.run, hrecords, update_rt, S₀, ‹records ≠ recordSaved›.symm]
          obtain ⟨v₁, hu₁, he₁⟩ := packNext_exec (body := body)
            (show [count, pad, src, saved, acc, buf, savedBlock, tmp].Nodup by simp_all)
            { v with sym := some c } S₀ xs (blocks.flatten ++ tail)
            (by simpa [S₀, ‹records ≠ src›.symm, ‹recordSaved ≠ src›.symm, List.append_assoc] using hsrc)
            (by simpa [S₀, ‹records ≠ count›.symm, ‹recordSaved ≠ count›.symm, hxs] using hcount)
            (by simpa [S₀, ‹records ≠ buf›.symm, ‹recordSaved ≠ buf›.symm] using hbuf)
            (by simpa [S₀, ‹records ≠ savedBlock›.symm, ‹recordSaved ≠ savedBlock›.symm] using hsavedBlock)
            (by simpa [S₀, ‹records ≠ tmp›.symm, ‹recordSaved ≠ tmp›.symm] using htmp)
          set S₁ : Stacks T A := { S₀ with R := (Function.update
            (Function.update (Function.update S₀.R src (blocks.flatten ++ tail)) saved (xs.reverse ++ S₀.R saved))
            acc (List.replicate (S₀.R pad).length (pairSym A false false) ++ xs.reverse ++ S₀.R acc)) }
          have e (r : Fin T) (h₁ : r ≠ src) (h₂ : r ≠ saved) (h₃ : r ≠ acc) :
              S₁.R r = S₀.R r := by simp [S₁, h₁, h₂, h₃]
          obtain ⟨v₂, hu₂, he₂⟩ := ih hlen' cs hcs'
            { v₁ with flag := (S₁.R records).head?.isSome } S₁
            (by simp [e _ ‹records ≠ src› ‹records ≠ saved› ‹records ≠ acc›, S₀, ‹records ≠ recordSaved›])
            (by simp [S₁, ‹src ≠ acc›, ‹src ≠ saved›])
            (by simpa [e _ ‹count ≠ src› ‹count ≠ saved› ‹count ≠ acc›, S₀,
              ‹records ≠ count›.symm, ‹recordSaved ≠ count›.symm] using hcount)
            (by simpa [e _ ‹src ≠ buf›.symm ‹saved ≠ buf›.symm ‹acc ≠ buf›.symm, S₀,
              ‹records ≠ buf›.symm, ‹recordSaved ≠ buf›.symm] using hbuf)
            (by simpa [e _ ‹src ≠ savedBlock›.symm ‹saved ≠ savedBlock›.symm ‹acc ≠ savedBlock›.symm, S₀,
              ‹records ≠ savedBlock›.symm, ‹recordSaved ≠ savedBlock›.symm] using hsavedBlock)
            (by simpa [e _ ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm ‹acc ≠ tmp›.symm, S₀,
              ‹records ≠ tmp›.symm, ‹recordSaved ≠ tmp›.symm] using htmp)
            (by simp [e _ ‹records ≠ src› ‹records ≠ saved› ‹records ≠ acc›, S₀, ‹records ≠ recordSaved›])
          have hpeek := Exec.act (body := body) (peekR records) (mk v₁ S₁)
          rw [peekR_run] at hpeek
          refine ⟨v₂, hu₂.trans hu₁, (Exec.loop_true (by simpa using hflag)
            (Exec.seq (hrun ▸ Exec.act (body := body) (popPush records recordSaved) (mk v S))
              (Exec.seq he₁ hpeek)) he₂).cast ?_ ?_⟩
          · simp [S₁, S₀, ‹records ≠ pad›.symm, ‹recordSaved ≠ pad›.symm,
              ‹pad ≠ src›, ‹pad ≠ saved›, ‹pad ≠ acc›, hxs]
            ring
          · congr 1
            ext1
            · rfl
            · rfl
            · rfl
            clear he₁ he₂ hpeek hrun hu₁ hu₂ ih hlen hlen' hcs hcs' hflag hrecords
              hsrc hcount hbuf hsavedBlock htmp e
            funext r
            simp (disch := first | assumption | (apply Ne.symm; assumption)) only
              [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                List.flatMap_cons, List.reverse_append, List.reverse_cons]
            simp only [Function.update_apply]
            split_ifs <;> subst_vars <;> simp_all [List.append_assoc]

theorem packLoop_exec {records recordSaved count pad src saved acc buf savedBlock tmp : Fin T}
    (hreg : [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp].Nodup)
    (a : ℕ) (blocks : List (List (Fin (A + 4)))) (hlen : ∀ xs ∈ blocks, xs.length = a)
    (cs : List (Fin (A + 4))) (hcs : cs.length = blocks.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hrecords : S.R records = cs) (hsrc : S.R src = blocks.flatten)
    (hcount : (S.R count).length = a)
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = [])
    (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (packLoopBody records recordSaved count pad src saved acc buf savedBlock tmp))
        (mk v S) (blocks.length * (16 * a + 4 * (S.R pad).length + 23) + 1)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R records []) recordSaved
            (cs.reverse ++ S.R recordSaved)) src []) saved
            (blocks.flatten.reverse ++ S.R saved)) acc
            ((blocks.flatMap fun xs => xs ++ List.replicate (S.R pad).length
              (pairSym A false false)).reverse ++ S.R acc)) }) := by
  simpa only [List.append_nil] using
    packLoop_prefix_exec hreg a blocks hlen cs hcs v S []
      hrecords (by simpa using hsrc) hcount hbuf hsavedBlock htmp hflag

/-- Equal-size blocks occupy their count times their common symbol length. -/
theorem length_flatten_blocks (a : ℕ) (blocks : List (List (Fin (A + 4))))
    (hlen : ∀ xs ∈ blocks, xs.length = a) : blocks.flatten.length = blocks.length * a := by
  induction blocks with
  | nil => simp
  | cons xs blocks ih =>
      have hx := hlen xs (by simp)
      have ht := ih (fun ys hy => hlen ys (by simp [hy]))
      simp [ht, hx, Nat.add_mul, Nat.add_comm]

/-- Pack all records, then restore the record counter and raw input stream. -/
def packBatch (records recordSaved count pad src saved acc buf savedBlock tmp dst : Fin T) :
    Pr P T Q A U :=
  .seq (.act (peekR records)) <|
  .seq (.loop (·.flag) (packLoopBody records recordSaved count pad src saved acc buf savedBlock tmp)) <|
  .seq (moveR recordSaved records id) <|
  .seq (moveR acc dst id) (moveR saved src id)

/-- Complete batch packing: only the destination changes, including when the batch or the
raw blocks are empty. All setup counters are shared across the batch. -/
theorem packBatch_prefix_exec {records recordSaved count pad src saved acc buf savedBlock tmp dst : Fin T}
    (hreg : [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp, dst].Nodup)
    (a : ℕ) (blocks : List (List (Fin (A + 4)))) (hlen : ∀ xs ∈ blocks, xs.length = a)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hrecords : (S.R records).length = blocks.length) (hsrc : S.R src = blocks.flatten ++ tail)
    (hcount : (S.R count).length = a)
    (hrecordSaved : S.R recordSaved = []) (hsaved : S.R saved = []) (hacc : S.R acc = [])
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packBatch records recordSaved count pad src saved acc buf savedBlock tmp dst)
        (mk v S)
        (blocks.length * (18 * a + 4 * (S.R pad).length + 2 * (a + (S.R pad).length) + 25) + 8)
        (mk v' { S with R := (Function.update S.R dst
          ((blocks.flatMap fun xs => xs ++ List.replicate (S.R pad).length
            (pairSym A false false)) ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  set packed := blocks.flatMap fun xs => xs ++ List.replicate (S.R pad).length (pairSym A false false)
  have hrawLen := length_flatten_blocks a blocks hlen
  have hpackedLen : packed.length = blocks.length * (a + (S.R pad).length) := by
    change ((blocks.map fun xs => xs ++ List.replicate (S.R pad).length
      (pairSym A false false)).flatten).length = _
    rw [← List.length_map (f := fun xs => xs ++ List.replicate (S.R pad).length
      (pairSym A false false)) (as := blocks)]
    apply length_flatten_blocks
    intro zs hz
    obtain ⟨xs, hx, rfl⟩ := List.mem_map.mp hz
    simp [hlen xs hx]
  have hpeek := Exec.act (body := body) (peekR records) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨v₁, hu₁, he₁⟩ := packLoop_prefix_exec (body := body)
    (show [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp].Nodup by simp_all)
    a blocks hlen (S.R records) hrecords { v with flag := (S.R records).head?.isSome } S tail
    rfl hsrc hcount hbuf hsavedBlock htmp rfl
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R records []) recordSaved
      ((S.R records).reverse ++ S.R recordSaved)) src tail) saved
      (blocks.flatten.reverse ++ S.R saved)) acc (packed.reverse ++ S.R acc)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body recordSaved records ‹records ≠ recordSaved›.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R recordSaved records id (S₁.R recordSaved) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body acc dst ‹acc ≠ dst› id v₂ S₂
  set S₃ : Stacks T A := { S₂ with R := movedR S₂.R acc dst id (S₂.R acc) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₃ S₃
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq hpeek (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)))).cast ?_ ?_⟩
  · have hlen₁ : (S₁.R recordSaved).length = blocks.length := by
      simp [S₁, ‹recordSaved ≠ acc›, ‹recordSaved ≠ saved›, ‹recordSaved ≠ src›,
        hrecordSaved, hrecords]
    have hlen₂ : (S₂.R acc).length = blocks.length * (a + (S.R pad).length) := by
      simp [S₂, S₁, movedR, ‹records ≠ acc›.symm, ‹recordSaved ≠ acc›.symm,
        hacc, hpackedLen]
    have hlen₃ : (S₃.R saved).length = blocks.length * a := by
      simp [S₃, S₂, S₁, movedR, ‹saved ≠ dst›, ‹saved ≠ acc›, ‹records ≠ saved›.symm,
        ‹recordSaved ≠ saved›.symm, hsaved, hrawLen]
    rw [hlen₁, hlen₂, hlen₃]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄ hpeek hu₁ hu₂ hu₃ hu₄ hlen hrecords hcount hbuf hsavedBlock htmp
    funext r
    simp (disch := first | assumption | (apply Ne.symm; assumption)) only
      [S₃, S₂, S₁, movedR, Function.update_self, Function.update_of_ne, List.map_id,
        hrecordSaved, hsaved, hacc, List.append_nil, List.reverse_reverse]
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [packed]


theorem packBatch_exec {records recordSaved count pad src saved acc buf savedBlock tmp dst : Fin T}
    (hreg : [records, recordSaved, count, pad, src, saved, acc, buf, savedBlock, tmp, dst].Nodup)
    (a : ℕ) (blocks : List (List (Fin (A + 4)))) (hlen : ∀ xs ∈ blocks, xs.length = a)
    (v : HS T Q A U) (S : Stacks T A)
    (hrecords : (S.R records).length = blocks.length) (hsrc : S.R src = blocks.flatten)
    (hcount : (S.R count).length = a)
    (hrecordSaved : S.R recordSaved = []) (hsaved : S.R saved = []) (hacc : S.R acc = [])
    (hbuf : S.R buf = []) (hsavedBlock : S.R savedBlock = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (packBatch records recordSaved count pad src saved acc buf savedBlock tmp dst)
        (mk v S)
        (blocks.length * (18 * a + 4 * (S.R pad).length + 2 * (a + (S.R pad).length) + 25) + 8)
        (mk v' { S with R := (Function.update S.R dst
          ((blocks.flatMap fun xs => xs ++ List.replicate (S.R pad).length
            (pairSym A false false)) ++ S.R dst)) }) := by
  simpa only [List.append_nil] using
    packBatch_prefix_exec hreg a blocks hlen v S []
      hrecords (by simpa using hsrc) hcount hrecordSaved hsaved hacc hbuf hsavedBlock htmp

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
