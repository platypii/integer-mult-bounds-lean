module

public import IntegerMultBounds.MathlibTM2.Host.GatherRecords
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! The record-level inverse of selection: consume a selected record or emit
one zero record. Both branches have the same structural execution contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def spreadRecordStep (width src acc tmp : Fin T) (f : Fin (A+4) → Bool)
    (zero : Fin (A+4)) : Pr P T Q A U :=
  .cond (fun v => f (v.sym.getD blank))
    (transfer width src acc tmp) (umulSym 1 zero width acc tmp)

theorem spreadRecordStep_exec (width src acc tmp : Fin T)
    (hreg : [width,src,acc,tmp].Nodup) (f : Fin (A+4) → Bool) (zero m : Fin (A+4))
    (w : ℕ) (word tail : List (Fin (A+4))) (hlen : word.length = w)
    (hzero : f m = false → word = List.replicate w zero)
    (v : HS T Q A U) (S : Stacks T A) (hsym : v.sym = some m)
    (hw : (S.R width).length = w)
    (hsrc : S.R src = (if f m then word else [])++tail) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (spreadRecordStep width src acc tmp f zero) (mk v S) (4*w+5)
        (mk v' {S with R := (Function.update (Function.update S.R src tail) acc
          (word.reverse++S.R acc))}) := by
  have hr := hreg
  regs_ne hr
  cases hb : f m with
  | true =>
    obtain ⟨v',hu,he⟩ := transfer_exec (body := body) hreg v S word tail
      (by simpa [hb] using hsrc) (hw.trans hlen.symm) htmp
    exact ⟨v',hu,(Exec.cond_true (by simp [hsym,hb]) he).cast (by rw [hlen]) rfl⟩
  | false =>
    obtain ⟨v',hu,he⟩ := umulSym_exec (body := body) 1 zero
      ‹width ≠ acc› ‹width ≠ tmp› ‹acc ≠ tmp› v S htmp
    have hs : S.R src = tail := by simpa [hb] using hsrc
    refine ⟨v',hu,(Exec.cond_false (by simp [hsym,hb]) he).cast (by rw [hw]) ?_⟩
    apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = src
    · subst i; simp [‹src ≠ acc›,hs]
    · by_cases ha : i = acc <;> simp [hi,ha,hzero hb,hw]

end IntegerMultBounds.MathlibTM2.Host
