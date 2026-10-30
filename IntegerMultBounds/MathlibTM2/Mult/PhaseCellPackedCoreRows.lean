module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.NLogN.PhaseCellCoreWindows

/-! Derive normalization row dimensions from a core-length word and native precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def preparePackedCoreRows (coreWord precision rows rowWidth work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (toUnary coreWord rows work saved tmp)
    (.seq (generateWordWidth precision work tmp)
      (.seq (unaryProduct rows work rowWidth saved tmp) (uclear work)))

def preparePackedCoreRowsCost (B q L : ℕ) : ℕ := 12*q+L*(8*q+47)+11*B+37

/-- Generate both L and L(2q+8) from ordinary retained inputs. The core word and
actual precision symbols restore; no unary row, word-width or product witness
is supplied. Only the two owned row headers change. -/
theorem preparePackedCoreRows_exec {coreWord precision rows rowWidth work saved tmp : Fin T}
    (hreg : [coreWord,precision,rows,rowWidth,work,saved,tmp].Nodup)
    (B q L : ℕ) (hL : L < 2^B) (v : HS T Q A U) (S : Stacks T A)
    (hword : S.R coreWord = binSyms B L) (hq : (S.R precision).length = q)
    (hblank : ∀ i ∈ [rows,rowWidth,work,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparePackedCoreRowsCost B q L ∧
      Exec body (preparePackedCoreRows coreWord precision rows rowWidth work saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R rows (List.replicate L tick))
          rowWidth (List.replicate (L*(2*q+8)) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (show [coreWord,rows,work,saved,tmp].Nodup by regs_nodup) hL v S hword
    (hblank work (by simp)) (hblank saved (by simp)) (hblank tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R rows (List.replicate L tick)}
  have he₁' : Exec body (toUnary coreWord rows work saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hblank rows (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := generateWordWidth_exec (body := body)
    (show [precision,work,tmp].Nodup by regs_nodup) q v₁ S₁
    (by simpa [S₁,‹precision ≠ rows›] using hq)
    (by simpa [S₁,‹rows ≠ work›.symm] using hblank work (by simp))
    (by simpa [S₁,‹rows ≠ tmp›.symm] using hblank tmp (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R work (List.replicate (2*q+8) tick)}
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (show [rows,work,rowWidth,saved,tmp].Nodup by regs_nodup) v₂ S₂
    (by simpa [S₂,S₁,‹work ≠ saved›.symm,‹rows ≠ saved›.symm] using hblank saved (by simp))
    (by simpa [S₂,S₁,‹work ≠ tmp›.symm,‹rows ≠ tmp›.symm] using hblank tmp (by simp))
  have hn₃' : n₃ ≤ L*(4*(2*q+8)+9)+4 := by simp [S₂,S₁,‹rows ≠ work›] at hn₃; exact hn₃
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R rowWidth (List.replicate (L*(2*q+8)) tick)}
  have he₃' : Exec body (unaryProduct rows work rowWidth saved tmp) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,‹rows ≠ work›,‹rowWidth ≠ work›,‹rows ≠ rowWidth›.symm,
      hblank rowWidth (by simp)] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) work v₃ S₃
  refine ⟨v₄,n₁+(8*q+9)+n₃+(2*(2*q+8)+2),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · unfold preparePackedCoreRowsCost
    nlinarith only [hn₁,hn₃']
  · simp [S₃,S₂,S₁,‹rowWidth ≠ work›.symm,Nat.add_assoc]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hw : i = work
    · subst i; simp [S₃,S₂,S₁, *, Ne.symm]
    by_cases hr : i = rows
    · subst i; simp [S₃,S₂,S₁, *, Ne.symm]
    by_cases hb : i = rowWidth
    · subst i; simp [S₃,S₂,S₁, *, Ne.symm]
    · simp [S₃,S₂,S₁,hw,hr,hb]

/-- Generated owned-core lengths inherit representability from the ambient
period word. The output dimensions use the core length, not the halo length. -/
theorem prepareOwnedCoreRows_exec {coreWord precision rows rowWidth work saved tmp : Fin T}
    (hreg : [coreWord,precision,rows,rowWidth,work,saved,tmp].Nodup)
    (B q s width k : ℕ) (hs : s < 2^B) (v : HS T Q A U) (S : Stacks T A)
    (hword : S.R coreWord = binSyms B (coreLength s width k)) (hq : (S.R precision).length = q)
    (hblank : ∀ i ∈ [rows,rowWidth,work,saved,tmp], S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ preparePackedCoreRowsCost B q (coreLength s width k) ∧
      Exec body (preparePackedCoreRows coreWord precision rows rowWidth work saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R rows
          (List.replicate (coreLength s width k) tick)) rowWidth
            (List.replicate (coreLength s width k*(2*q+8)) tick))}) := by
  have hL : coreLength s width k ≤ s :=
    (min_le_right width (s-coreStart width k)).trans (Nat.sub_le s _)
  exact preparePackedCoreRows_exec hreg B q (coreLength s width k) (hL.trans_lt hs) v S hword hq hblank

def releasePackedCoreRows (rows rowWidth : Fin T) : Pr P T Q A U :=
  .seq (uclear rowWidth) (uclear rows)

theorem releasePackedCoreRows_exec {rows rowWidth : Fin T} (hne : rows ≠ rowWidth)
    (L w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = L) (hwidth : (S.R rowWidth).length = L*w) :
    ∃ v', v'.user = v.user ∧
      Exec body (releasePackedCoreRows rows rowWidth) (mk v S) (2*L*(w+1)+4)
        (mk v' {S with R := Function.update (Function.update S.R rowWidth []) rows []}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) rowWidth v S
  let S₁ : Stacks T A := {S with R := Function.update S.R rowWidth []}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec (body := body) rows v₁ S₁
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ rfl⟩
  simp only [S₁,Function.update_of_ne hne,hrows,hwidth]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
