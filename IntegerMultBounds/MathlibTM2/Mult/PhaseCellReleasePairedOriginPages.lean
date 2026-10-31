module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Retire both owned coordinate pages using their shared count and width.
Borrowed suffixes and the width master survive; the owned count is released. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def releasePairedOriginPages (cells width volume ambient offsets saved tmp : Fin T) : Pr P T Q A U :=
  .seq (unaryProduct cells width volume saved tmp)
    (.seq (discardPrefix volume ambient saved tmp)
      (.seq (discardPrefix volume offsets saved tmp) (.seq (uclear volume) (uclear cells))))

def releasePairedOriginPagesCost (B V : ℕ) := 18*(B*V)+11*B+20

theorem releasePairedOriginPages_exec
    (cells width volume ambient offsets saved tmp : Fin T)
    (hreg : [cells,width,volume,ambient,offsets,saved,tmp].Nodup)
    (B V : ℕ) (ambientPage localPage ambientTail localTail : List (Fin (A+4)))
    (haLen : ambientPage.length = B*V) (hlLen : localPage.length = B*V)
    (v : HS T Q A U) (S : Stacks T A)
    (hB : (S.R cells).length = B) (hV : (S.R width).length = V)
    (ha : S.R ambient = ambientPage++ambientTail) (hl : S.R offsets = localPage++localTail)
    (hclean : ∀ k ∈ [volume,saved,tmp], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releasePairedOriginPagesCost B V ∧
      Exec body (releasePairedOriginPages cells width volume ambient offsets saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R ambient ambientTail)
          offsets localTail) cells [])}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := unaryProduct_exec (body := body)
    (a := cells) (b := width) (dst := volume) (t₁ := saved) (t₂ := tmp) (by regs_nodup)
    v S (hclean _ (by simp)) (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R volume (List.replicate (B*V) tick)}
  have he₁' : Exec body (unaryProduct cells width volume saved tmp) (mk v S) m₁ (mk v₁ M) := by
    simpa only [hB,hV,hclean volume (by simp),List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body)
    (count := volume) (src := ambient) (trash := saved) (tmp := tmp) (by regs_nodup)
    ambientPage ambientTail v₁ M
    (by simpa [M,‹volume ≠ ambient›.symm] using ha) (by simp [M,haLen])
    (by simpa [M,‹volume ≠ saved›.symm] using hclean saved (by simp))
    (by simpa [M,‹volume ≠ tmp›.symm] using hclean tmp (by simp))
  let K : Stacks T A := {M with R := Function.update M.R ambient ambientTail}
  obtain ⟨v₃,hu₃,he₃⟩ := discardPrefix_exec (body := body)
    (count := volume) (src := offsets) (trash := saved) (tmp := tmp) (by regs_nodup)
    localPage localTail v₂ K
    (by simpa [K,M,‹ambient ≠ offsets›.symm,‹volume ≠ offsets›.symm] using hl)
    (by simp [K,M,‹volume ≠ ambient›,hlLen])
    (by simpa [K,M,‹ambient ≠ saved›.symm,‹volume ≠ saved›.symm] using hclean saved (by simp))
    (by simpa [K,M,‹ambient ≠ tmp›.symm,‹volume ≠ tmp›.symm] using hclean tmp (by simp))
  let J : Stacks T A := {K with R := Function.update K.R offsets localTail}
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) volume v₃ J
  let H : Stacks T A := {J with R := Function.update J.R volume []}
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec (body := body) cells v₄ H
  have hvolume : (J.R volume).length = B*V := by simp [J,K,M,‹volume ≠ offsets›,‹volume ≠ ambient›]
  have hcells : (H.R cells).length = B := by
    simp [H,J,K,M,‹cells ≠ volume›,‹cells ≠ offsets›,‹cells ≠ ambient›,hB]
  refine ⟨v₅,m₁+((6*ambientPage.length+6)+((6*localPage.length+6)+
    ((2*(J.R volume).length+2)+(2*(H.R cells).length+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,?_⟩
  · rw [hB,hV] at hm₁
    rw [haLen,hlLen,hvolume,hcells]
    unfold releasePairedOriginPagesCost
    nlinarith only [hm₁]
  · have hex := Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))
    have hend : {H with R := Function.update H.R cells []} =
        {S with R := (Function.update (Function.update (Function.update S.R ambient ambientTail)
          offsets localTail) cells [])} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk : k = volume
      · subst k
        simp [H,J,K,M,‹cells ≠ volume›.symm,‹volume ≠ offsets›,‹volume ≠ ambient›,hclean volume (by simp)]
      · simp [H,J,K,M,Function.update_apply,hk]
    simpa only [releasePairedOriginPages,hend] using hex

theorem releasePairedOriginPages_native (cells width volume ambient offsets saved tmp : Fin T) :
    mnNativePushBound 2 (releasePairedOriginPages (P := P) (Q := Q) (A := A) (U := U)
      cells width volume ambient offsets saved tmp) := by
  simp [releasePairedOriginPages,unaryProduct,discardPrefix,ucopy,umulSym,popPush,scanP,transfer,transferAct,
    moveR,moveStep,scanR,keepIn,uclear,drainR,popDo,whileR,peekR,pushN,mnNativePushBound,mnActPush]

theorem releasePairedOriginPages_exec_within
    (cells width volume ambient offsets saved tmp : Fin T)
    (hreg : [cells,width,volume,ambient,offsets,saved,tmp].Nodup)
    (B V : ℕ) (ambientPage localPage ambientTail localTail : List (Fin (A+4)))
    (haLen : ambientPage.length = B*V) (hlLen : localPage.length = B*V)
    (v : HS T Q A U) (S : Stacks T A)
    (hB : (S.R cells).length = B) (hV : (S.R width).length = V)
    (ha : S.R ambient = ambientPage++ambientTail) (hl : S.R offsets = localPage++localTail)
    (hclean : ∀ k ∈ [volume,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releasePairedOriginPagesCost B V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*releasePairedOriginPagesCost B V) depth (releasePairedOriginPages cells width volume ambient offsets saved tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R ambient ambientTail)
          offsets localTail) cells [])}) := by
  obtain ⟨v',m,hu,hm,he⟩ := releasePairedOriginPages_exec cells width volume ambient offsets saved tmp hreg
    B V ambientPage localPage ambientTail localTail haLen hlLen v S hB hV ha hl hclean
  exact ⟨v',m,hu,hm,mn_native_exec_within he 2 (releasePairedOriginPages_native _ _ _ _ _ _ _) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hm) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
