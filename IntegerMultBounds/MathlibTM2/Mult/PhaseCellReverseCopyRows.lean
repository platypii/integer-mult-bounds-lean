module

public import IntegerMultBounds.MathlibTM2.Host.RestoringRowScan
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Copy uniform rows into reverse row order while restoring the original
source. This instantiates the structural restoring scan with native prefix work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def reverseCopyRows (count savedCount width source archive dst saved tmp : Fin T) : Pr P T Q A U :=
  restoringRowScan count savedCount source archive
    (.seq (copyPrefix width source dst saved tmp) (transfer width source archive tmp))

def reverseCopyRowsCost (N V : ℕ) := N*(16*V+19)+6

theorem reverseCopyRows_exec_within (count savedCount width source archive dst saved tmp : Fin T)
    (hreg : [count,savedCount,width,source,archive,dst,saved,tmp].Nodup)
    (V : ℕ) (rows : List (List (Fin (A+4)))) (hlen : ∀ row ∈ rows, row.length = V)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = rows.length) (hwidth : (S.R width).length = V)
    (hsource : S.R source = rows.flatten++borrowed)
    (hfresh : ∀ k ∈ [savedCount,archive,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ reverseCopyRowsCost rows.length V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*reverseCopyRowsCost rows.length V) depth
        (reverseCopyRows count savedCount width source archive dst saved tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R dst (rows.reverse.flatten++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  have hscan : [count,savedCount,source,archive,dst].Nodup := by regs_nodup
  obtain ⟨v',n,hu,hn,he⟩ := restoringRowScan_exec (body := body) count savedCount source archive dst hscan
    (.seq (copyPrefix width source dst saved tmp) (transfer width source archive tmp))
    (14*V+14) rows id id borrowed v S (by simpa using hsource) (hfresh archive (by simp))
    hcount (hfresh savedCount (by simp)) (by
      intro row hrow v₀ F tail hframe hsrc
      have hw : (F.R width).length = V := by
        rw [hframe width (by simp_all [ne_comm])]
        exact hwidth
      have hs : F.R saved = [] := by rw [hframe saved (by simp_all [ne_comm])]; exact hfresh saved (by simp)
      have ht : F.R tmp = [] := by rw [hframe tmp (by simp_all [ne_comm])]; exact hfresh tmp (by simp)
      obtain ⟨v₁,hu₁,he₁⟩ := copyPrefix_exec (body := body) (count := width) (src := source)
        (dst := dst) (saved := saved) (tmp := tmp) (by regs_nodup) v₀ F row tail hsrc
        (by rw [hw,hlen row hrow]) hs ht
      let M : Stacks T A := {F with R := Function.update F.R dst (row++F.R dst)}
      obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := width) (src := source)
        (dst := archive) (tmp := tmp) (by regs_nodup) v₁ M row tail
        (by simpa [M,‹source ≠ dst›] using hsrc)
        (by simpa [M,‹width ≠ dst›,hlen row hrow] using hw)
        (by simpa [M,‹dst ≠ tmp›.symm] using ht)
      refine ⟨v₂,(10*row.length+10)+(4*row.length+4),hu₂.trans hu₁,by rw [hlen row hrow]; omega,
        (Exec.seq he₁ he₂).cast rfl ?_⟩
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hkSrc : k = source
      · subst k; simp [M,‹source ≠ archive›,‹source ≠ dst›]
      by_cases hkArc : k = archive
      · subst k; simp [M,‹archive ≠ dst›]
      · simp [M,Function.update_apply,hkSrc,hkArc])
  have hn' : n ≤ reverseCopyRowsCost rows.length V := by
    have hh := length_flatten_const rows hlen
    simp only [List.flatMap_id] at hn
    unfold reverseCopyRowsCost
    rw [hh] at hn
    nlinarith only [hn]
  have he' : Exec body (reverseCopyRows count savedCount width source archive dst saved tmp) (mk v S) n
      (mk v' {S with R := Function.update S.R dst (rows.reverse.flatten++S.R dst)}) := by
    simpa only [reverseCopyRows,List.flatMap_id] using he
  refine ⟨v',n,hu,hn',mn_native_exec_within he' 2 ?_ depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn') _)⟩
  simp [reverseCopyRows,restoringRowScan,copyPrefix,transfer,transferAct,copyR,copyStep,
    scanP,scanR,drainR,popDo,popPush,keepIn,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
