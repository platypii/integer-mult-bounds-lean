module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Fast.TableVM

/-! Publish selected binary table fields as a reusable owned packet prefix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def publishBinaryHeaders (rg : TblR n → Fin T) (dst saved tmp : Fin T) : List (Fin n) → Pr P T Q A U
  | [] => .act .done
  | i::fields => .seq (publishBinaryHeaders rg dst saved tmp fields)
      (copyPrefix (rg .wr) (rg (.v i)) dst saved tmp)

theorem publishBinaryHeaders_exec {rg : TblR n → Fin T} (hrg : Function.Injective rg)
    (dst saved tmp : Fin T) (hreg : [dst,saved,tmp].Nodup)
    (hsep : ∀ k ∈ [dst,saved,tmp], ∀ r, rg r ≠ k)
    (fields : List (Fin n)) (W : ℕ) (wl nl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt n A) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ fields.length*(10*W+10)+1 ∧
      Exec body (publishBinaryHeaders rg dst saved tmp fields) (mk v S) m
        (mk v' {S with R := (Function.update S.R dst
          (fields.flatMap (fun i => binSyms W (st.val i))++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  induction fields generalizing v S with
  | nil =>
    refine ⟨v,1,rfl,by simp,?_⟩
    simpa [publishBinaryHeaders] using Exec.act (body := body) .done (mk v S)
  | cons i fields ih =>
    obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := ih v S hS hsaved htmp
    let S₁ : Stacks T A := {S with R := (Function.update S.R dst
      (fields.flatMap (fun i => binSyms W (st.val i))++S.R dst))}
    have hh₁ : tblHolds rg S₁ (tblRho W wl nl st) := by
      intro r
      simpa [S₁,hsep dst (by simp) r] using hS r
    have hc : [rg .wr,rg (.v i),dst,saved,tmp].Nodup := by
      simp [List.nodup_cons,hrg.eq_iff,hsep,‹dst ≠ saved›,‹dst ≠ tmp›,‹saved ≠ tmp›,
        (hsep dst (by simp) (.v i)).symm,(hsep saved (by simp) (.v i)).symm,
        (hsep tmp (by simp) (.v i)).symm]
    obtain ⟨v₂,hu₂,he₂⟩ := copyPrefix_exec (body := body) hc v₁ S₁ (binSyms W (st.val i)) []
      (by simpa [tblRho] using hh₁ (.v i))
      (by rw [hh₁ .wr]; simpa [tblRho,binSyms] using hwl)
      (by simpa [S₁,‹dst ≠ saved›.symm] using hsaved)
      (by simpa [S₁,‹dst ≠ tmp›.symm] using htmp)
    refine ⟨v₂,m₁+(10*W+10),hu₂.trans hu₁,by simp only [List.length_cons]; nlinarith,
      (Exec.seq he₁ he₂).cast (by simp) ?_⟩
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = dst <;> simp [S₁,hk,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
