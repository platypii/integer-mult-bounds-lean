module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkDimensionBankStock

/-! Generate an encoded payload count, move exactly that prefix to its consumer,
and retire the counters. Both suffixes and every other register survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generatedPrefixHandoff (cells rowCount width rows words src dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct cells rowCount rows saved tmp)
    (.seq (unaryProduct rows width words saved tmp)
      (.seq (takePrefix words src dst saved tmp) (clearWords [rows,words])))

theorem generatedPrefixHandoff_native (cells rowCount width rows words src dst saved tmp : Fin T) :
    mnNativePushBound 2 (generatedPrefixHandoff (P := P) (Q := Q) (A := A) (U := U)
      cells rowCount width rows words src dst saved tmp) := by
  refine ⟨unaryProduct_native _ _ _ _ _,unaryProduct_native _ _ _ _ _,takePrefix_native _ _ _ _ _,?_⟩
  simp [clearWords,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

def generatedPrefixHandoffCost (cells rows width : ℕ) : ℕ :=
  12*(cells*rows*width)+15*(cells*rows)+9*cells+19

/-- Count generation and handoff cost only linear encoded-payload traffic. -/
theorem generatedPrefixHandoffCost_le (N L w : ℕ) (hL : 1 ≤ L) (hw : 1 ≤ w) :
    generatedPrefixHandoffCost N L w ≤ 36*N*L*w+19 := by
  have hNL : N*L ≤ N*L*w := Nat.le_mul_of_pos_right _ hw
  have hN : N ≤ N*L*w := by
    have hh := Nat.le_mul_of_pos_right N (Nat.mul_le_mul hL hw)
    simpa only [Nat.mul_assoc] using hh
  unfold generatedPrefixHandoffCost
  nlinarith only [hNL,hN]

theorem generatedPrefixHandoff_exec
    {cells rowCount width rows words src dst saved tmp : Fin T}
    (hreg : [cells,rowCount,width,rows,words,src,dst,saved,tmp].Nodup)
    (N L w : ℕ) (xs tail : List (Fin (A+4))) (hlen : xs.length = N*L*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R cells).length = N) (hL : (S.R rowCount).length = L) (hw : (S.R width).length = w)
    (hsource : S.R src = xs++tail)
    (hfresh : ∀ k ∈ [rows,words,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedPrefixHandoffCost N L w ∧
      Exec body (generatedPrefixHandoff cells rowCount width rows words src dst saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := unaryProduct_exec (body := body)
    (show [cells,rowCount,rows,saved,tmp].Nodup by regs_nodup) v S
    (hfresh saved (by simp)) (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R rows (List.replicate (N*L) tick)}
  have he₁' : Exec body (unaryProduct cells rowCount rows saved tmp) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hN,hL,hfresh rows (by simp),List.append_nil,S₁] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (show [rows,width,words,saved,tmp].Nodup by regs_nodup) v₁ S₁
    (by simp [S₁,Ne.symm ‹rows ≠ saved›,hfresh saved (by simp)])
    (by simp [S₁,Ne.symm ‹rows ≠ tmp›,hfresh tmp (by simp)])
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R words (List.replicate (N*L*w) tick)}
  have he₂' : Exec body (unaryProduct rows width words saved tmp) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,hw,‹width ≠ rows›,Ne.symm ‹rows ≠ words›,hfresh words (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := takePrefix_exec (body := body)
    (show [words,src,dst,saved,tmp].Nodup by regs_nodup) v₂ S₂ xs tail
    (by simpa [S₂,S₁,Ne.symm ‹words ≠ src›,Ne.symm ‹rows ≠ src›] using hsource)
    (by simp [S₂,hlen])
    (by simp [S₂,S₁,Ne.symm ‹words ≠ saved›,Ne.symm ‹rows ≠ saved›,hfresh saved (by simp)])
    (by simp [S₂,S₁,Ne.symm ‹words ≠ tmp›,Ne.symm ‹rows ≠ tmp›,hfresh tmp (by simp)])
  let S₃ : Stacks T A := {S₂ with R := (Function.update (Function.update S₂.R src tail) dst (xs++S₂.R dst))}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [rows,words]
    (by simp [‹rows ≠ words›]) v₃ S₃
  have hclear : 2*([rows,words].map (fun r => (S₃.R r).length)).sum+2*[rows,words].length+1 =
      2*(N*L)+2*(N*L*w)+5 := by
    simp [S₃,S₂,S₁,‹rows ≠ dst›,‹rows ≠ src›,‹rows ≠ words›,‹words ≠ dst›,‹words ≠ src›]
    omega
  have hfinal : {S₃ with R := fun k => if k ∈ [rows,words] then [] else S₃.R k} =
      {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hRows : k = rows
    · subst k; simp [hfresh rows (by simp),‹rows ≠ dst›,‹rows ≠ src›]
    by_cases hWords : k = words
    · subst k; simp [hfresh words (by simp),‹words ≠ dst›,‹words ≠ src›]
    simp [S₃,S₂,S₁,Function.update_apply,hRows,hWords,Ne.symm ‹rows ≠ dst›,Ne.symm ‹words ≠ dst›]
  rw [hclear,hfinal] at he₄
  refine ⟨v₄,n₁+(n₂+((6*xs.length+6)+(2*(N*L)+2*(N*L*w)+5))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))⟩
  simp only [hN,hL] at hn₁
  have hn₂' : n₂ ≤ (N*L)*(4*w+9)+4 := by
    simpa [S₁,hw,‹width ≠ rows›] using hn₂
  unfold generatedPrefixHandoffCost
  rw [hlen]
  nlinarith only [hn₁,hn₂']

/-- The same handoff execution has a data-linear bound on every configuration. -/
theorem generatedPrefixHandoff_within {cells rowCount width rows words src dst saved tmp : Fin T}
    {N L w n : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (generatedPrefixHandoff cells rowCount width rows words src dst saved tmp) z n z')
    (hn : n ≤ generatedPrefixHandoffCost N L w) (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+2*generatedPrefixHandoffCost N L w)
      depth (generatedPrefixHandoff cells rowCount width rows words src dst saved tmp) z n z' :=
  mn_native_exec_within he 2 (generatedPrefixHandoff_native _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
