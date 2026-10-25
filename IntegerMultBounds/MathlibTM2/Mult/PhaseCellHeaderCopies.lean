module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! Copy retained ordinary headers into a private solver bank. Separation of
all sources from all destinations makes the structural list reusable unchanged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def copyUnaryHeaders (tmp : Fin T) : List (Fin T × Fin T) → Pr P T Q A U
  | [] => .act .done
  | (src,dst)::rs => .seq (ucopy src dst tmp) (copyUnaryHeaders tmp rs)

def copyUnaryHeadersCost (value : Fin T → ℕ) (rs : List (Fin T × Fin T)) : ℕ :=
  (rs.map (fun r => 4*value r.1+4)).sum+1

theorem copyUnaryHeaders_exec (tmp : Fin T) (rs : List (Fin T × Fin T))
    (hregs : ∀ r ∈ rs, [r.1,r.2,tmp].Nodup)
    (hsep : ∀ r ∈ rs, ∀ p ∈ rs, r.2 ≠ p.1)
    (value : Fin T → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : ∀ r ∈ rs, (S.R r.1).length = value r.1) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (copyUnaryHeaders tmp rs) (mk v S) (copyUnaryHeadersCost value rs)
        (mk v' { S with R := unaryCopiesR value S.R rs }) := by
  induction rs generalizing v S with
  | nil =>
    refine ⟨v, rfl, ?_⟩
    simpa [copyUnaryHeaders, copyUnaryHeadersCost, unaryCopiesR, Action.run] using
      Exec.act (body := body) .done (mk v S)
  | cons r rs ih =>
    have hr := hregs r (by simp)
    regs_ne hr
    obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec (body := body) (a := r.1) (b := r.2) (t := tmp)
      ‹r.1 ≠ r.2› ‹r.1 ≠ tmp› ‹r.2 ≠ tmp› v S htmp
    let S₁ : Stacks T A := { S with R := Function.update S.R r.2 (List.replicate (value r.1) tick ++ S.R r.2) }
    have he₁' : Exec body (ucopy r.1 r.2 tmp) (mk v S) (4*value r.1+4) (mk v₁ S₁) := by
      simpa [S₁, hsrc r (by simp)] using he₁
    obtain ⟨v₂, hu₂, he₂⟩ := ih (fun p hp => hregs p (by simp [hp]))
      (fun p hp q hq => hsep p (by simp [hp]) q (by simp [hq])) v₁ S₁ (by
        intro p hp
        simpa [S₁, (hsep r (by simp) p (by simp [hp])).symm] using hsrc p (by simp [hp]))
      (by simpa [S₁, ‹r.2 ≠ tmp›.symm] using htmp)
    refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁' he₂).cast ?_ rfl⟩
    simp [copyUnaryHeadersCost]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
