module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSplitComponents

/-! Pair the two ordered real output batches in place, preserving later keys. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def pairComplexPrefix (count src buf saved tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src saved tmp)
    (.seq (moveR saved buf id)
      (.seq (pairComponents count buf src tmp) (moveR tmp src id)))

/-- The real half and imaginary half have equal coefficient counts. Pair them
without moving the borrowed suffix; the symbol counter is consumed and all
private buffers restore. No condition on the unused imaginary word parts is
needed. -/
theorem pairComplexPrefix_exec {count src buf saved tmp : Fin T}
    (hreg : [count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    (w : ℕ) (xs ys : List GaussianInt) (hlen : xs.length = ys.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (xs++ys)++tail)
    (hcount : (S.R count).length = xs.length*w)
    (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 12*(xs.length*w)+10 ∧
      Exec body (pairComplexPrefix count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R count []) src
          (cstream A w (List.zipWith pairComponentWord xs ys)++tail))}) := by
  have hr := hreg
  regs_ne hr
  let X := cstream A w xs
  let Y := cstream A w ys
  let Z := cstream A w (List.zipWith pairComponentWord xs ys)
  have hX : X.length = xs.length*w := by simp [X]
  have hY : X.length = Y.length := by simp [X,Y,hlen]
  have hZ : Z.length = X.length := by simp [Z,X,hlen]
  have hzip : List.zipWith pairComponentSymbol X Y = Z := pairComponentSymbol_cstream hA w xs ys hlen
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body)
    (show [count,src,saved,tmp].Nodup by regs_nodup) v S X (Y++tail)
    (by simpa [X,Y,List.append_assoc] using hsrc) (by simpa [hX] using hcount) htmp
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src (Y++tail)) saved X.reverse)}
  have he₁' : Exec body (transfer count src saved tmp) (mk v S) (4*X.length+4) (mk v₁ S₁) := by
    simpa [S₁,hsaved] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) saved buf ‹buf ≠ saved›.symm id v₁ S₁
  let S₂ : Stacks T A := {S₁ with R := (Function.update (Function.update S₁.R saved []) buf X)}
  have he₂' : Exec body (moveR saved buf id) (mk v₁ S₁) (2*X.length+2) (mk v₂ S₂) := by
    simpa [S₂,S₁,movedR,‹src ≠ buf›.symm,‹buf ≠ saved›,hbuf] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := pairComponents_exec (body := body)
    (show [count,buf,src,tmp].Nodup by regs_nodup) X Y [] tail hY v₂ S₂
    (by simpa [S₂,S₁,‹count ≠ buf›,‹count ≠ saved›,‹count ≠ src›,hX] using hcount)
    (by simp [S₂]) (by simp [S₂,S₁,‹src ≠ buf›,‹src ≠ saved›])
  let S₃ : Stacks T A := {S₂ with R := (Function.update (Function.update
    (Function.update (Function.update S₂.R buf []) src tail) tmp Z.reverse) count [])}
  have he₃' : Exec body (pairComponents count buf src tmp) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,hzip,S₂,S₁,‹saved ≠ tmp›.symm,‹buf ≠ tmp›.symm,‹src ≠ tmp›.symm,htmp] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec (body := body) tmp src ‹src ≠ tmp›.symm id v₃ S₃
  have h₃tmp : S₃.R tmp = Z.reverse := by simp [S₃,‹count ≠ tmp›.symm]
  refine ⟨v₄,(4*X.length+4)+(2*X.length+2)+n₃+(2*Z.length+2),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · rw [hZ,hX]
    rw [hX] at hn₃
    omega
  · simp [h₃tmp,Nat.add_assoc]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp only [S₃,S₂,S₁,movedR,Function.update_apply,List.map_id]
    split_ifs <;> subst_vars <;> simp_all [Z,hbuf,hsaved,htmp]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
