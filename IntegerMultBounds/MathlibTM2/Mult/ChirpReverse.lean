module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Reverse coefficient order while preserving the words

A symbol reversal would reverse the low-bit-first representation inside every coefficient.
This program instead copies one fixed-width word at a time to the destination. The source,
both unary counters and all workspace are restored, including with spectator suffixes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Prepend one word unchanged, saving its original symbols for source restoration. -/
def reverseNext (width src dst saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix width src dst buf tmp) (transfer width src saved tmp)

theorem reverseNext_exec {width src dst saved buf tmp : Fin T}
    (hreg : [width, src, dst, saved, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs rest : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ rest) (hlen : (S.R width).length = xs.length)
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseNext width src dst saved buf tmp) (mk v S) (14 * xs.length + 14)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update S.R src rest) saved (xs.reverse ++ S.R saved)) dst
          (xs ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyPrefix_exec (body := body)
    (show [width, src, dst, buf, tmp].Nodup by simp_all) v S xs rest hsrc hlen hbuf htmp
  set S₁ : Stacks T A := { S with R := (Function.update S.R dst (xs ++ S.R dst)) }
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body)
    (show [width, src, saved, tmp].Nodup by simp_all) v₁ S₁ xs rest
    (by simpa [S₁, ‹src ≠ dst›] using hsrc)
    (by simpa [S₁, ‹width ≠ dst›] using hlen)
    (by simp [S₁, ‹dst ≠ tmp›.symm, htmp])
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext r
  simp only [S₁, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

/-- Consume one word-count symbol, copy the next word, and test the count again. -/
def reverseLoopBody (records recordSaved width src dst saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (popPush records recordSaved))
    (.seq (reverseNext width src dst saved buf tmp) (.act (peekR records)))

/-- Structural loop invariant over arbitrary equal-width words. -/
theorem reverseLoop_exec {records recordSaved width src dst saved buf tmp : Fin T}
    (hreg : [records, recordSaved, width, src, dst, saved, buf, tmp].Nodup)
    (w : ℕ) (words : List (List (Fin (A + 4)))) (hlen : ∀ xs ∈ words, xs.length = w)
    (cs : List (Fin (A + 4))) (hcs : cs.length = words.length)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hrecords : S.R records = cs) (hsrc : S.R src = words.flatten ++ tail)
    (hwidth : (S.R width).length = w) (hbuf : S.R buf = []) (htmp : S.R tmp = [])
    (hflag : v.flag = cs.head?.isSome) :
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag) (reverseLoopBody records recordSaved width src dst saved buf tmp))
        (mk v S) (words.length * (14 * w + 17) + 1)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R records []) recordSaved
            (cs.reverse ++ S.R recordSaved)) src tail) saved
            (words.flatten.reverse ++ S.R saved)) dst
            (words.reverse.flatten ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  induction words generalizing cs v S with
  | nil =>
      have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcs)
      simp only [hnil] at hrecords hflag ⊢
      refine ⟨v, rfl, ?_⟩
      have he := Exec.loop_false (body := body)
        (p := reverseLoopBody records recordSaved width src dst saved buf tmp)
        (show v.flag = false by simpa using hflag) (s := mk v S)
      convert he using 1 <;> simp only [List.length_nil, Nat.zero_mul, Nat.zero_add,
        List.flatten_nil, List.reverse_nil, List.nil_append]
      congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext r
      simp only [Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
  | cons xs words ih =>
      cases cs with
      | nil => simp at hcs
      | cons c cs =>
          have hxs : xs.length = w := hlen xs (by simp)
          set S₀ : Stacks T A := { S with R := (Function.update (Function.update S.R records cs)
            recordSaved (c :: S.R recordSaved)) }
          have hrun : (popPush records recordSaved : Act T Q A U).run (mk v S) =
              mk { v with sym := some c } S₀ := by
            simp [popPush, Action.run, hrecords, update_rt, S₀, ‹records ≠ recordSaved›.symm]
          obtain ⟨v₁, hu₁, he₁⟩ := reverseNext_exec (body := body)
            (show [width, src, dst, saved, buf, tmp].Nodup by simp_all)
            { v with sym := some c } S₀ xs (words.flatten ++ tail)
            (by simpa [S₀, ‹records ≠ src›.symm, ‹recordSaved ≠ src›.symm,
              List.flatten_cons, List.append_assoc] using hsrc)
            (by simpa [S₀, ‹records ≠ width›.symm, ‹recordSaved ≠ width›.symm, hxs] using hwidth)
            (by simpa [S₀, ‹records ≠ buf›.symm, ‹recordSaved ≠ buf›.symm] using hbuf)
            (by simpa [S₀, ‹records ≠ tmp›.symm, ‹recordSaved ≠ tmp›.symm] using htmp)
          set S₁ : Stacks T A := { S₀ with R := (Function.update (Function.update
            (Function.update S₀.R src (words.flatten ++ tail)) saved (xs.reverse ++ S₀.R saved))
            dst (xs ++ S₀.R dst)) }
          have e (r : Fin T) (h₁ : r ≠ src) (h₂ : r ≠ saved) (h₃ : r ≠ dst) :
              S₁.R r = S₀.R r := by simp [S₁, h₁, h₂, h₃]
          obtain ⟨v₂, hu₂, he₂⟩ := ih (fun ys hy => hlen ys (by simp [hy])) cs
            (by simpa using hcs) { v₁ with flag := (S₁.R records).head?.isSome } S₁
            (by simp [e _ ‹records ≠ src› ‹records ≠ saved› ‹records ≠ dst›, S₀,
              ‹records ≠ recordSaved›])
            (by simp [S₁, ‹src ≠ dst›, ‹src ≠ saved›])
            (by simpa [e _ ‹width ≠ src› ‹width ≠ saved› ‹width ≠ dst›, S₀,
              ‹records ≠ width›.symm, ‹recordSaved ≠ width›.symm] using hwidth)
            (by simpa [e _ ‹src ≠ buf›.symm ‹saved ≠ buf›.symm ‹dst ≠ buf›.symm, S₀,
              ‹records ≠ buf›.symm, ‹recordSaved ≠ buf›.symm] using hbuf)
            (by simpa [e _ ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm ‹dst ≠ tmp›.symm, S₀,
              ‹records ≠ tmp›.symm, ‹recordSaved ≠ tmp›.symm] using htmp)
            (by simp [e _ ‹records ≠ src› ‹records ≠ saved› ‹records ≠ dst›, S₀,
              ‹records ≠ recordSaved›])
          have hpeek := Exec.act (body := body) (peekR records) (mk v₁ S₁)
          rw [peekR_run] at hpeek
          refine ⟨v₂, hu₂.trans hu₁, (Exec.loop_true (by simpa using hflag)
            (Exec.seq (hrun ▸ Exec.act (body := body) (popPush records recordSaved) (mk v S))
              (Exec.seq he₁ hpeek)) he₂).cast ?_ ?_⟩
          · rw [hxs]
            simp only [List.length_cons]
            ring
          · congr 1
            ext1
            · rfl
            · rfl
            · rfl
            clear he₁ he₂ hpeek hrun hu₁ hu₂ ih hlen hcs hflag hrecords hsrc hwidth hbuf htmp e
            funext r
            simp (disch := first | assumption | (apply Ne.symm; assumption)) only
              [S₁, S₀, Function.update_self, Function.update_of_ne, List.flatten_cons,
                List.reverse_append, List.reverse_cons, List.flatten_append,
                List.flatten_cons, List.flatten_nil, List.append_nil]
            simp only [Function.update_apply]
            split_ifs <;> subst_vars <;> simp_all [List.append_assoc]

/-- Reverse a prefix of equal-width words and restore both input and counters. -/
def reverseWords (records recordSaved width src dst saved buf tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR records)) <|
  .seq (.loop (·.flag) (reverseLoopBody records recordSaved width src dst saved buf tmp)) <|
  .seq (moveR recordSaved records id) (moveR saved src id)

theorem reverseWords_exec {records recordSaved width src dst saved buf tmp : Fin T}
    (hreg : [records, recordSaved, width, src, dst, saved, buf, tmp].Nodup)
    (w : ℕ) (words : List (List (Fin (A + 4)))) (hlen : ∀ xs ∈ words, xs.length = w)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hrecords : (S.R records).length = words.length)
    (hsrc : S.R src = words.flatten ++ tail) (hwidth : (S.R width).length = w)
    (hrecordSaved : S.R recordSaved = []) (hsaved : S.R saved = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseWords records recordSaved width src dst saved buf tmp) (mk v S)
        (words.length * (16 * w + 19) + 6)
        (mk v' { S with R := Function.update S.R dst (words.reverse.flatten ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := reverseLoop_exec (body := body) hreg w words hlen (S.R records)
    hrecords { v with flag := (S.R records).head?.isSome } S tail rfl hsrc hwidth hbuf htmp rfl
  set S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update (Function.update (Function.update S.R records []) recordSaved
      ((S.R records).reverse ++ S.R recordSaved)) src tail) saved
      (words.flatten.reverse ++ S.R saved)) dst (words.reverse.flatten ++ S.R dst)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body recordSaved records ‹records ≠ recordSaved›.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R recordSaved records id (S₁.R recordSaved) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₂ S₂
  have flatLength (ws : List (List (Fin (A + 4))))
      (hs : ∀ xs ∈ ws, xs.length = w) : ws.flatten.length = ws.length * w := by
    induction ws with
    | nil => simp
    | cons xs ws ih =>
      rw [List.flatten_cons, List.length_append, hs xs (by simp),
        ih (fun ys hy => hs ys (by simp [hy])), List.length_cons]
      ring
  have hflat := flatLength words hlen
  have hp := Exec.act (body := body) (peekR records) (mk v S)
  rw [peekR_run] at hp
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁),
    (Exec.seq hp (Exec.seq he₁ (Exec.seq he₂ he₃))).cast ?_ ?_⟩
  · simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₂, S₁, movedR, hrecordSaved, hsaved, hrecords, hflat]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ hp hu₁ hu₂ hu₃
    funext r
    simp (disch := first | assumption | (apply Ne.symm; assumption)) only
      [S₂, S₁, movedR, Function.update_self, Function.update_of_ne,
        hrecordSaved, hsaved, List.append_nil, List.map_id, List.reverse_reverse]
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

/-- Coefficient reversal preserves the low-bit-first word encoding. -/
theorem reverseWords_coeffs_exec {records recordSaved width src dst saved buf tmp : Fin T}
    (hreg : [records, recordSaved, width, src, dst, saved, buf, tmp].Nodup)
    (w : ℕ) (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (tail : List (Fin (A + 4))) (hrecords : (S.R records).length = xs.length)
    (hsrc : S.R src = cstream A w xs ++ tail) (hwidth : (S.R width).length = w)
    (hrecordSaved : S.R recordSaved = []) (hsaved : S.R saved = [])
    (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reverseWords records recordSaved width src dst saved buf tmp) (mk v S)
        (xs.length * (16 * w + 19) + 6)
        (mk v' { S with R := Function.update S.R dst (cstream A w xs.reverse ++ S.R dst) }) := by
  simpa only [List.length_map, List.map_reverse, List.flatMap_def, cstream] using
    reverseWords_exec (body := body) hreg w (xs.map (csyms A w))
      (by intro ys hy; obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy; simp [csyms])
      v S tail (by simpa using hrecords) (by simpa [cstream, List.flatMap_def] using hsrc)
      hwidth hrecordSaved hsaved hbuf htmp

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
