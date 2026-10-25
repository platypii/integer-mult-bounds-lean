module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Node.TopWord

/-! # A counted floor-slice word pass through the existing stream executor -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def floorSliceWord (src dst skip width rest tmp : Fin T) : Pr P T Q A U :=
  .seq (usub skip src tmp) (.seq (transfer width src dst tmp)
    (.seq (usub rest src tmp) (.act (peekR src))))

def FloorSliceReady (skip width rest tmp : Fin T) (a b e : ℕ) (R : Regs T A) : Prop :=
  (R skip).length = a ∧ (R width).length = b ∧ (R rest).length = e ∧ R tmp = []

theorem floorSliceWord_spec {src dst skip width rest tmp : Fin T}
    (hreg : [src, dst, skip, width, rest, tmp].Nodup) (a b e : ℕ) :
    TopWordSpec body (floorSliceWord src dst skip width rest tmp) src dst
      (FloorSliceReady skip width rest tmp a b e) (a + b + e) (fun xs => (xs.drop a).take b)
      (4 * (a + b + e) + 13) := by
  have hreg' := hreg
  regs_ne hreg'
  intro xs tail v S hlen hsrc hg
  obtain ⟨ha, hb, he, ht⟩ := hg
  obtain ⟨v₁, hu₁, he₁⟩ := usub_exec (body := body) ‹src ≠ skip›.symm ‹skip ≠ tmp› ‹src ≠ tmp› v S ht
  let S₁ : Stacks T A := { S with R := Function.update S.R src ((xs ++ tail).drop a) }
  have he₁' : Exec body (usub skip src tmp) (mk v S) (4 * a + 4) (mk v₁ S₁) := by
    simpa only [ha, hsrc] using he₁
  let ys := (xs.drop a).take b
  let more := (xs.drop (a + b)) ++ tail
  have hsplit : (xs ++ tail).drop a = ys ++ more := by
    have h := List.take_append_drop b (xs.drop a)
    rw [List.drop_drop] at h
    dsimp [ys, more]
    rw [List.drop_append_of_le_length (by omega), ← List.append_assoc]
    exact congrArg (fun zs => zs ++ tail) h.symm
  have hylen : ys.length = b := by simp [ys, hlen]; omega
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body)
    (show [width, src, dst, tmp].Nodup by regs_nodup) v₁ S₁ ys more
    (by simpa [S₁] using hsplit) (by simpa [S₁, ‹src ≠ width›.symm, hylen] using hb)
    (by simpa [S₁, ‹src ≠ tmp›.symm] using ht)
  let S₂ : Stacks T A := { S₁ with R := (Function.update (Function.update S₁.R src more) dst
    (ys.reverse ++ S₁.R dst)) }
  obtain ⟨v₃, hu₃, he₃⟩ := usub_exec (body := body) ‹src ≠ rest›.symm ‹rest ≠ tmp› ‹src ≠ tmp› v₂ S₂
    (by simpa [S₂, S₁, ‹src ≠ tmp›.symm, ‹dst ≠ tmp›.symm] using ht)
  have hrest₂ : (S₂.R rest).length = e := by
    simpa [S₂, S₁, ‹src ≠ rest›.symm, ‹dst ≠ rest›.symm] using he
  have htail : more.drop e = tail := by
    dsimp [more]
    have hlen' : (xs.drop (a + b)).length = e := by simp [hlen]
    rw [List.drop_left' hlen']
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R src tail }
  have he₃' : Exec body (usub rest src tmp) (mk v₂ S₂) (4 * e + 4) (mk v₃ S₃) := by
    simpa only [hrest₂, S₂, Function.update_of_ne ‹src ≠ dst›, Function.update_self, htail] using he₃
  let v₄ : HS T Q A U := { v₃ with flag := tail.head?.isSome }
  have he₄ : Exec body (.act (peekR src)) (mk v₃ S₃) 1 (mk v₄ S₃) := by
    have hex := Exec.act (body := body) (peekR src) (mk v₃ S₃)
    rw [peekR_run] at hex
    simpa [S₃, v₄] using hex
  refine ⟨v₄, hu₃.trans (hu₂.trans hu₁), rfl,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · rw [hylen]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hs : k = src
    · subst k; simp [S₃, ‹src ≠ dst›]
    by_cases hd : k = dst
    · subst k; simp [S₃, S₂, S₁, ys, ‹src ≠ dst›.symm]
    simp [S₃, S₂, S₁, hs, hd, ys]

theorem floorSliceReady_frame {src dst skip width rest tmp : Fin T}
    (hreg : [src, dst, skip, width, rest, tmp].Nodup) (a b e : ℕ) :
    TopWordFrame src dst (FloorSliceReady skip width rest tmp (A := A) a b e) := by
  have hreg' := hreg
  regs_ne hreg'
  intro R xs ys ⟨ha, hb, he, ht⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp_all [ne_comm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
