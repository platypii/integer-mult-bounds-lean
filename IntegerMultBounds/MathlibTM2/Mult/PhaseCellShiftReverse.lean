module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking

/-! # Shifted reversal of a borrowed generator column

Save the head word, reverse the remaining coefficient words with the existing
structural loop, restore the source, and prepend a zero word.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def shiftReverse (records recordSaved width src dst saved buf tmp head : Fin T) : Pr P T Q A U :=
  .seq (transfer width src head tmp)
    (.seq (reverseWords records recordSaved width src dst saved buf tmp)
      (.seq (moveR head src id) (copyR width dst buf (fun _ => pairSym A false false))))

/-- Only the destination changes. Source and destination suffixes are arbitrary. -/
theorem shiftReverse_exec {records recordSaved width src dst saved buf tmp head : Fin T}
    (hreg : [records, recordSaved, width, src, dst, saved, buf, tmp, head].Nodup)
    (w : ℕ) (x : GaussianInt) (xs : List GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hrecords : (S.R records).length = xs.length)
    (hsrc : S.R src = cstream A w (x :: xs) ++ tail) (hwidth : (S.R width).length = w)
    (hclean : ∀ k ∈ [recordSaved, saved, buf, tmp, head], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (shiftReverse records recordSaved width src dst saved buf tmp head) (mk v S)
        (xs.length * (16 * w + 19) + 10 * w + 16)
        (mk v' { S with R := Function.update S.R dst (cstream A w (0 :: xs.reverse) ++ S.R dst) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hhead := hclean head (by simp)
  have hbuf := hclean buf (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body)
    (show [width, src, head, tmp].Nodup by simp_all [ne_comm]) v S (csyms A w x) (cstream A w xs ++ tail)
    (by simpa [cstream_cons, List.append_assoc] using hsrc) (by simpa using hwidth) (hclean tmp (by simp))
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R src
    (cstream A w xs ++ tail)) head ((csyms A w x).reverse ++ S.R head)) }
  obtain ⟨v₂, hu₂, he₂⟩ := reverseWords_coeffs_exec (body := body)
    (show [records, recordSaved, width, src, dst, saved, buf, tmp].Nodup by simp_all [ne_comm])
    w xs v₁ S₁ tail
    (by simpa [S₁, ‹records ≠ src›, ‹records ≠ head›] using hrecords)
    (by simp [S₁, ‹src ≠ head›])
    (by simpa [S₁, ‹width ≠ src›, ‹width ≠ head›] using hwidth)
    (by simpa [S₁, ‹recordSaved ≠ src›, ‹recordSaved ≠ head›] using hclean recordSaved (by simp))
    (by simpa [S₁, ‹src ≠ saved›.symm, ‹saved ≠ head›] using hclean saved (by simp))
    (by simpa [S₁, ‹src ≠ buf›.symm, ‹buf ≠ head›] using hbuf)
    (by simpa [S₁, ‹src ≠ tmp›.symm, ‹tmp ≠ head›] using hclean tmp (by simp))
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (cstream A w xs.reverse ++ S₁.R dst) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body head src ‹src ≠ head›.symm id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R head src id (S₂.R head) }
  obtain ⟨v₄, hu₄, he₄⟩ := copyR_exec body width dst buf ‹width ≠ dst› ‹width ≠ buf› ‹dst ≠ buf›
    (fun _ => pairSym A false false) v₃ S₃
    (by simp [S₃, S₂, S₁, movedR, ‹buf ≠ head›, ‹src ≠ buf›.symm, ‹dst ≠ buf›.symm, hbuf])
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp [S₃, S₂, S₁, movedR, hhead, ‹dst ≠ head›.symm, ‹width ≠ head›,
      ‹width ≠ src›, ‹width ≠ dst›, hwidth]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₃, S₂, S₁, movedR, Function.update_apply, List.map_id,
      hhead, List.append_nil, List.reverse_reverse, List.reverse_append]
    split_ifs <;> subst_vars <;>
      simp_all [cstream_cons, csyms_zero, hsrc, List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
