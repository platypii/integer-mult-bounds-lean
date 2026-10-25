module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Fast.Output

/-! # Remove the padded tail of the final chirp block

Keep a counted prefix, erase the remaining stream and restore the prefix in order.
The program depends only on register placement, including for an empty output.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpCrop (count src saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src saved tmp) (.seq (clearR src) (moveR saved src id))

/-- Crop a symbol stream with exact cost and complete restoration of its working bank. -/
theorem chirpCrop_exec {count src saved tmp : Fin T}
    (hreg : [count, src, saved, tmp].Nodup)
    (xs rest : List (Fin (A + 4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs ++ rest) (hcount : (S.R count).length = xs.length)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpCrop count src saved tmp) (mk v S)
        (6 * xs.length + 2 * rest.length + 8)
        (mk v' { S with R := Function.update S.R src xs }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body) hreg v S xs rest hsrc hcount htmp
  let S₁ : Stacks T A := { S with R := (Function.update
    (Function.update S.R src rest) saved (xs.reverse ++ S.R saved)) }
  obtain ⟨v₂, hu₂, he₂⟩ := clearR_exec body src v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R src [] }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body saved src ‹src ≠ saved›.symm id v₂ S₂
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [S₂, S₁, hsaved, ‹src ≠ saved›, ‹src ≠ saved›.symm]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext r
    simp only [S₂, S₁, movedR, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all

/-- Crop the final partial block at a coefficient boundary. -/
theorem chirpCrop_stream_exec {count src saved tmp : Fin T}
    (hreg : [count, src, saved, tmp].Nodup)
    (w t : ℕ) (xs : List GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hcount : (S.R count).length = (min t xs.length) * w)
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpCrop count src saved tmp) (mk v S)
        (6 * ((min t xs.length) * w) + 2 * ((xs.length - t) * w) + 8)
        (mk v' { S with R := Function.update S.R src (cstream A w (xs.take t)) }) := by
  obtain ⟨v', hu, he⟩ := chirpCrop_exec (body := body) hreg
    (cstream A w (xs.take t)) (cstream A w (xs.drop t)) v S
    (by rw [← cstream_append, List.take_append_drop]; exact hsrc)
    (by simpa using hcount) hsaved htmp
  exact ⟨v', hu, he.cast (by simp) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
