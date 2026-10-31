module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData

/-! Consume one replica's padding and publish its real core rows in one sweep.
Following replicas and the borrowed output suffix remain outside ownership. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A s L : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem paddedWindowPublication_exec
    (padRows wordWidth retireCount control savedControl gap window src dst acc trash tmp : Fin T)
    (hreg : [padRows,wordWidth,retireCount,control,savedControl,gap,window,src,dst,acc,trash,tmp].Nodup)
    (windows : PublicationWindows s L) (w missing : ℕ) (hw1 : 1 ≤ w)
    (paddedRows rows : List (List GaussianInt))
    (hlen : rows.length = windows.origins.length)
    (hrows : ∀ row ∈ rows, row.length = L) (hpadded : ∀ row ∈ paddedRows, row.length = L)
    (hmissing : missing+rows.length = paddedRows.length)
    (hreal : paddedRows.flatten.drop (missing*L) = rows.flatten)
    (E sourceTail outputTail : List (Fin (A+4))) (hE : E.length = s*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w paddedRows.flatten++sourceTail)
    (hpadRows : (S.R padRows).length = missing*L) (hwidth : (S.R wordWidth).length = w)
    (hc : S.R control = gatherControls A (windows.gaps w))
    (hdst : S.R dst = E++outputTail) (hw : (S.R window).length = L*w)
    (hclean : ∀ i ∈ [retireCount,savedControl,gap,acc,trash,tmp], S.R i = [])
    :
    ∃ v' n, v'.user = v.user ∧ n ≤ retireCountedLineCost (missing*L) w+35*s*w+6 ∧
      Exec body (.seq (retireCountedLine padRows wordWidth src retireCount trash tmp)
        (scatterBatch control savedControl gap window src dst acc trash tmp)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src sourceTail)
          dst (scatterRows (L*w) E (cstream A w rows.flatten)
            (windows.gaps w)++outputTail))}) := by
  have hr := hreg
  regs_ne hr
  let paddingWords := paddedRows.flatten.take (missing*L)
  have hprefix : paddingWords.length = missing*L := by
    dsimp only [paddingWords]
    rw [List.length_take,length_flatten_const paddedRows hpadded]
    exact min_eq_left (Nat.mul_le_mul_right L (by omega))
  have hsplit : paddedRows.flatten = paddingWords++rows.flatten := by
    have h := List.take_append_drop (missing*L) paddedRows.flatten
    rw [hreal] at h
    exact h.symm
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := retireCountedLine_exec (body := body)
    padRows wordWidth src retireCount trash tmp (by regs_nodup) (missing*L) w
    (cstream A w paddingWords) (cstream A w rows.flatten++sourceTail)
    (by rw [length_cstream,hprefix]) v S hpadRows hwidth
    (by rw [hsrc,hsplit,cstream_append,List.append_assoc])
    (hclean _ (by simp)) (hclean _ (by simp)) (hclean _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R src (cstream A w rows.flatten++sourceTail)}
  have hstable (i : Fin T) (hi : i ≠ src) : M.R i = S.R i := by simp [M,hi]
  have hwords : (cstream A w rows.flatten).length = windows.origins.length*(L*w) := by
    rw [length_cstream,length_flatten_const rows hrows,hlen,Nat.mul_assoc]
  obtain ⟨v₂,hu₂,he₂⟩ := windowScatter_exec (body := body)
    (control := control) (savedControl := savedControl) (gap := gap) (window := window)
    (src := src) (dst := dst) (acc := acc) (trash := trash) (tmp := tmp) (by regs_nodup)
    windows w E (cstream A w rows.flatten) sourceTail outputTail hE hwords v₁ M
    (by rw [hstable _ ‹control ≠ src›]; exact hc)
    (by rw [hstable _ ‹src ≠ dst›.symm]; exact hdst) (by simp [M])
    (by rw [hstable _ ‹window ≠ src›]; exact hw)
    (by
      intro i hi
      have hne : i ≠ src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl
        all_goals first | assumption | (apply Ne.symm; assumption)
      rw [hstable i hne]
      apply hclean i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      exact Or.inr hi)
  have hn₂ := windows.cost_le w hw1
  refine ⟨v₂,n₁+windows.cost w,hu₂.trans hu₁,by omega,?_⟩
  have he := Exec.seq he₁ he₂
  simpa [M,‹src ≠ dst›.symm] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
