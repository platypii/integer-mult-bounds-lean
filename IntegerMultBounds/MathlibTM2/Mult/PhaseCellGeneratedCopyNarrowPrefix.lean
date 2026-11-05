module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedPrefixCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyNarrowPrefix
import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedCopyNarrowPrefix
    (cells rowCount wide rows count src dst saved tmp width work zero extra : Fin T) : Pr P T Q A U :=
  .seq (UnarySetup.program (encodedPrefixCountOps cells rowCount wide rows count saved tmp))
    (.seq (copyNarrowPrefix count src dst saved tmp wide width work zero extra) (uclear count))

def generatedCopyNarrowPrefixCost (N L W w : ℕ) : ℕ :=
  encodedPrefixCountCost N L W+copyNarrowPrefixCost W w (N*L)+2*(N*L*W)+2

theorem generatedCopyNarrowPrefixCost_le (N L W w : ℕ) (hL : 1 ≤ L)
    (hW : 1 ≤ W) (hw : w ≤ W) :
    generatedCopyNarrowPrefixCost N L W w ≤ 60*N*L*W+8*W+37 := by
  have hNL := Nat.le_mul_of_pos_right (N*L) hW
  have hN : N ≤ N*L*W := by
    have h := Nat.le_mul_of_pos_right N (Nat.mul_le_mul hL hW)
    simpa only [Nat.mul_assoc] using h
  have hwidth := Nat.mul_le_mul_left (N*L) hw
  unfold generatedCopyNarrowPrefixCost encodedPrefixCountCost copyNarrowPrefixCost
  have hdiff : W-w+w = W := Nat.sub_add_cancel hw
  nlinarith only [hNL,hN,hwidth,hw,hdiff]

/-- Copy and resize a batch using only retained dimensions. The encoded count
and its intermediate product are generated and retired inside the program. -/
theorem generatedCopyNarrowPrefix_exec
    (cells rowCount wide rows count src dst saved tmp width work zero extra : Fin T)
    (hreg : [cells,rowCount,wide,rows,count,src,dst,saved,tmp,width,work,zero,extra].Nodup)
    (N L W w : ℕ) (hW : 1 ≤ W) (hw : w ≤ W) (xs : List GaussianInt)
    (hlen : xs.length = N*L) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R cells).length = N) (hL : (S.R rowCount).length = L)
    (hwide : (S.R wide).length = W) (hwidth : (S.R width).length = w)
    (hsrc : S.R src = cstream A W xs++tail)
    (hfresh : ∀ k ∈ [rows,count,dst,saved,tmp,work,zero,extra], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedCopyNarrowPrefixCost N L W w ∧
      Exec body (generatedCopyNarrowPrefix cells rowCount wide rows count src dst saved tmp width work zero extra)
        (mk v S) n (mk v' {S with R := Function.update S.R dst (cstream A w xs)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := encodedPrefixCount_exec (body := body)
    cells rowCount wide rows count saved tmp (by regs_nodup) N L W v S hN hL hwide
    (by intro k hk; exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let M : Stacks T A := {S with R := Function.update S.R count (List.replicate (N*L*W) tick)}
  have hM (k : Fin T) (hk : k ≠ count) : M.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨v₂,hu₂,he₂⟩ := copyNarrowPrefix_exec body count src dst saved tmp wide width work zero extra
    (by regs_nodup) W w hW hw xs tail v₁ M
    (by simpa only [hM src (Ne.symm ‹count ≠ src›)] using hsrc)
    (by simp [M,hlen])
    (by simpa only [hM wide ‹wide ≠ count›] using hwide)
    (by simpa only [hM width (Ne.symm ‹count ≠ width›)] using hwidth)
    (by rw [hM dst (Ne.symm ‹count ≠ dst›)]; exact hfresh dst (by simp))
    (by rw [hM saved (Ne.symm ‹count ≠ saved›)]; exact hfresh saved (by simp))
    (by rw [hM tmp (Ne.symm ‹count ≠ tmp›)]; exact hfresh tmp (by simp))
    (by rw [hM work (Ne.symm ‹count ≠ work›)]; exact hfresh work (by simp))
    (by rw [hM zero (Ne.symm ‹count ≠ zero›)]; exact hfresh zero (by simp))
    (by rw [hM extra (Ne.symm ‹count ≠ extra›)]; exact hfresh extra (by simp))
  let H : Stacks T A := {M with R := Function.update M.R dst (cstream A w xs)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body count v₂ H
  have hc : (H.R count).length = N*L*W := by simp [H,M,‹count ≠ dst›]
  have hframe : {H with R := Function.update H.R count []} =
      {S with R := Function.update S.R dst (cstream A w xs)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = count
    · subst k; simp [‹count ≠ dst›,hfresh count (by simp)]
    · simp [H,M,Function.update_apply,hk]
  rw [hc,hframe] at he₃
  rw [hlen] at he₂
  refine ⟨v₃,n₁+(copyNarrowPrefixCost W w (N*L)+(2*(N*L*W)+2)),
    hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  unfold generatedCopyNarrowPrefixCost
  omega

theorem generatedCopyNarrowPrefix_native
    (cells rowCount wide rows count src dst saved tmp width work zero extra : Fin T) :
    mnNativePushBound 3 (generatedCopyNarrowPrefix (P := P) (Q := Q) (A := A) (U := U)
      cells rowCount wide rows count src dst saved tmp width work zero extra) := by
  refine ⟨mnNativePushBound_mono (by decide) (encodedPrefixCount_native ..),
    copyNarrowPrefix_native ..,?_⟩
  simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem generatedCopyNarrowPrefix_within
    {cells rowCount wide rows count src dst saved tmp width work zero extra : Fin T}
    {N L W w n : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (generatedCopyNarrowPrefix cells rowCount wide rows count src dst saved tmp width work zero extra) z n z')
    (hn : n ≤ generatedCopyNarrowPrefixCost N L W w) (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+3*generatedCopyNarrowPrefixCost N L W w)
      depth (generatedCopyNarrowPrefix cells rowCount wide rows count src dst saved tmp width work zero extra) z n z' :=
  mn_native_exec_within he 3 (generatedCopyNarrowPrefix_native ..) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
