module

public import IntegerMultBounds.MathlibTM2.Host.RestoringRowScan
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Copy uniform rows in source order, preserving an arbitrary source suffix.
Accumulate reversed symbols during the restoring scan, then reverse once.
The program uses only retained row count and width, not a supplied total volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def copyRowsOrdered (count savedCount width source archive reversed dst saved tmp : Fin T) : Pr P T Q A U :=
  .seq (restoringRowScan count savedCount source archive
    (.seq (transfer width source archive tmp) (copyPrefix width archive reversed saved tmp)))
    (moveR reversed dst id)

def copyRowsOrderedCost (N V : ℕ) := N*(18*V+19)+8

theorem copyRowsOrdered_exec (count savedCount width source archive reversed dst saved tmp : Fin T)
    (hreg : [count,savedCount,width,source,archive,reversed,dst,saved,tmp].Nodup)
    (V : ℕ) (rows : List (List (Fin (A+4)))) (hlen : ∀ row ∈ rows, row.length = V)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hwidth : (S.R width).length = V)
    (hsource : S.R source = rows.flatten++borrowed)
    (hfresh : ∀ k ∈ [savedCount,archive,reversed,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ copyRowsOrderedCost rows.length V ∧
      Exec body (copyRowsOrdered count savedCount width source archive reversed dst saved tmp)
        (mk v S) n (mk v' {S with R := Function.update S.R dst (rows.flatten++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  have lengthRows : ∀ xs : List (List (Fin (A+4))), (∀ row ∈ xs, row.length = V) →
      xs.flatten.length = xs.length*V := by
    intro xs hx
    induction xs with
    | nil => simp
    | cons row xs ih =>
      have hh := hx row (by simp)
      have ht : ∀ row ∈ xs, row.length = V := by intro row h; exact hx row (by simp [h])
      simp only [List.flatten_cons,List.length_append,List.length_cons,hh,ih ht,Nat.succ_mul]
      omega
  have hlenFlat := lengthRows rows hlen
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := restoringRowScan_exec (body := body) count savedCount source archive reversed
    (by regs_nodup) (.seq (transfer width source archive tmp) (copyPrefix width archive reversed saved tmp))
    (14*V+14) rows id List.reverse borrowed v S (by simpa using hsource)
    (hfresh archive (by simp)) hcount (hfresh savedCount (by simp)) (by
      intro row hrow vi F tail hframe hsrc
      have hw : (F.R width).length = row.length := by rw [hframe width (by simp_all [ne_comm]),hwidth,hlen row hrow]
      have hs : F.R saved = [] := by rw [hframe saved (by simp_all [ne_comm])]; exact hfresh saved (by simp)
      have ht : F.R tmp = [] := by rw [hframe tmp (by simp_all [ne_comm])]; exact hfresh tmp (by simp)
      obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := width) (src := source)
        (dst := archive) (tmp := tmp) (by regs_nodup) vi F row tail hsrc hw ht
      let J : Stacks T A := {F with R := Function.update (Function.update F.R source tail) archive (row.reverse++F.R archive)}
      obtain ⟨v₃,hu₃,he₃⟩ := copyPrefix_exec (body := body) (count := width) (src := archive)
        (dst := reversed) (saved := saved) (tmp := tmp) (by regs_nodup) v₂ J row.reverse (F.R archive)
        (by simp [J]) (by simpa [J,‹width ≠ archive›,‹width ≠ source›] using hw)
        (by simpa [J,‹archive ≠ saved›.symm,‹source ≠ saved›.symm] using hs)
        (by simpa [J,‹archive ≠ tmp›.symm,‹source ≠ tmp›.symm] using ht)
      refine ⟨v₃,(4*row.length+4)+(10*row.reverse.length+10),hu₃.trans hu₂,
        by rw [List.length_reverse,hlen row hrow]; omega,(Exec.seq he₂ he₃).cast rfl ?_⟩
      apply congrArg (mk v₃)
      simp [J,‹archive ≠ reversed›.symm,‹source ≠ reversed›.symm])
  let J : Stacks T A := {S with R := Function.update S.R reversed (rows.flatten.reverse)}
  have hrev : rows.reverse.flatMap List.reverse = rows.flatten.reverse := by
    simp [List.flatMap_def,List.reverse_flatten]
  have he₁' : Exec body (restoringRowScan count savedCount source archive
      (.seq (transfer width source archive tmp) (copyPrefix width archive reversed saved tmp)))
      (mk v S) n (mk v₁ J) := by
    simpa only [hrev,hfresh reversed (by simp),List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body reversed dst ‹reversed ≠ dst› id v₁ J
  refine ⟨v₂,n+(2*rows.flatten.length+2),hu₂.trans hu₁,?_,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp only [List.flatMap_def,List.map_id,hlenFlat] at hn
    rw [hlenFlat]
    unfold copyRowsOrderedCost
    nlinarith [hn]
  · simp [J]
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [J,movedR,Function.update_apply,List.map_id,List.reverse_reverse]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
