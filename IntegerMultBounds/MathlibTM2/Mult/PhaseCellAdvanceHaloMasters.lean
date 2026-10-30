module

public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Advance retained unary endpoints by the difference of two binary origins.
Only the movement is decoded; the existing endpoint stacks are never scanned. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def advanceUnaryPair (word a b work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary word a work saved tmp) (toUnary word b work saved tmp)

theorem advanceUnaryPair_exec {word a b work saved tmp : Fin T}
    (hreg : [word,a,b,work,saved,tmp].Nodup) {V d : ℕ} (hd : d < 2^V)
    (v : HS T Q A U) (S : Stacks T A) (hword : S.R word = binSyms V d)
    (hwork : S.R work = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 12*d+22*V+12 ∧
      Exec body (advanceUnaryPair word a b work saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R a (List.replicate d tick++S.R a))
          b (List.replicate d tick++S.R b))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear body
    (a := word) (z := a) (w := work) (t := saved) (t₂ := tmp)
    (by regs_nodup) hd v S hword hwork hsaved htmp
  let H : Stacks T A := {S with R := Function.update S.R a (List.replicate d tick++S.R a)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear body
    (a := word) (z := b) (w := work) (t := saved) (t₂ := tmp)
    (by regs_nodup) hd v₁ H
    (by simpa [H,‹word ≠ a›] using hword)
    (by simpa [H,‹a ≠ work›.symm] using hwork)
    (by simpa [H,‹a ≠ saved›.symm] using hsaved)
    (by simpa [H,‹a ≠ tmp›.symm] using htmp)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by omega,?_⟩
  simpa only [advanceUnaryPair,H,Function.update_of_ne ‹a ≠ b›.symm] using Exec.seq he₁ he₂

def advanceHaloMasters (old next delta a b work saved tmp borrow : Fin T) : Pr P T Q A U :=
  .seq (bsub next old delta work saved tmp borrow)
    (.seq (advanceUnaryPair delta a b work saved tmp) (uclear delta))

def advanceHaloMastersCost (V d : ℕ) : ℕ := 12*d+32*V+22

theorem advanceHaloMasters_exec {old next delta a b work saved tmp borrow : Fin T}
    (hreg : [old,next,delta,a,b,work,saved,tmp,borrow].Nodup)
    {V x y : ℕ} (hxy : x ≤ y) (hy : y < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hold : S.R old = binSyms V x) (hnext : S.R next = binSyms V y)
    (hfresh : ∀ k ∈ [delta,work,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ advanceHaloMastersCost V (y-x) ∧
      Exec body (advanceHaloMasters old next delta a b work saved tmp borrow) (mk v S) n
        (mk v' {S with R := (Function.update
          (Function.update S.R a (List.replicate (y-x) tick++S.R a))
          b (List.replicate (y-x) tick++S.R b))}) := by
  have hr := hreg
  regs_ne hr
  have hx : x < 2^V := lt_of_le_of_lt hxy hy
  have hd : y-x < 2^V := by omega
  have hmod : (y+2^V-x)%2^V = y-x := by
    rw [show y+2^V-x = (y-x)+2^V by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  obtain ⟨v₁,hu₁,_,_,he₁⟩ := bsub_exec body
    (a := next) (b := old) (c := delta) (tx := work) (ty := saved) (tz := tmp) (cy := borrow)
    (by regs_nodup) ‹next ≠ borrow›.symm ‹old ≠ borrow›.symm hy hx v S hnext hold
    (hfresh work (by simp)) (hfresh saved (by simp)) (hfresh tmp (by simp))
  let H : Stacks T A := {S with R := Function.update S.R delta (binSyms V (y-x))}
  have he₁' : Exec body (bsub next old delta work saved tmp borrow) (mk v S) (8*V+8) (mk v₁ H) := by
    simpa only [H,hmod,hfresh delta (by simp),List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := advanceUnaryPair_exec (body := body)
    (word := delta) (a := a) (b := b) (work := work) (saved := saved) (tmp := tmp)
    (by regs_nodup) hd v₁ H (by simp [H])
    (by simpa [H,‹delta ≠ work›.symm] using hfresh work (by simp))
    (by simpa [H,‹delta ≠ saved›.symm] using hfresh saved (by simp))
    (by simpa [H,‹delta ≠ tmp›.symm] using hfresh tmp (by simp))
  let J : Stacks T A := {H with R := (Function.update
    (Function.update H.R a (List.replicate (y-x) tick++H.R a))
    b (List.replicate (y-x) tick++H.R b))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body delta v₂ J
  have hlen : (J.R delta).length = V := by
    simp [J,H,‹delta ≠ b›,‹delta ≠ a›,length_binSyms]
  refine ⟨v₃,(8*V+8)+(n₂+(2*V+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁' (Exec.seq he₂ (he₃.cast (by rw [hlen]) rfl))).cast rfl ?_⟩
  · unfold advanceHaloMastersCost
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases ha : k = a
    · subst k; simp [J,H,‹a ≠ b›,‹delta ≠ a›.symm]
    by_cases hb : k = b
    · subst k; simp [J,H,‹delta ≠ b›.symm]
    by_cases hd : k = delta
    · subst k; simp [J,H,‹delta ≠ a›,‹delta ≠ b›,hfresh delta (by simp)]
    simp [J,H,Function.update_of_ne ha,Function.update_of_ne hb,Function.update_of_ne hd]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
