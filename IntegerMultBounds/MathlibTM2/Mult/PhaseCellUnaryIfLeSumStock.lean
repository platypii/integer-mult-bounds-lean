module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryIfLeSum
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryIfLtStock

/-! Restoring unary sum comparison preserves a separately bounded continuation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem unaryIfLeSum_exec_within {a b band endpoint work tmp : Fin T}
    (hreg : [a,b,band,endpoint,work,tmp].Nodup) (yes no : Pr P T Q A U) (n m W budget reserve depth : ℕ)
    (S S' : Stacks T A) (hn : (S.R a).length = n) (hm : (S.R b).length = m)
    (hW : (S.R band).length = W) (hfresh : ∀ k ∈ [endpoint,work,tmp], S.R k = [])
    (hbranch : ∀ vi : HS T Q A U, ∃ v' steps, v'.user = vi.user ∧ steps ≤ budget ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi S)+depth+reserve)
        depth (if n ≤ m+W then yes else no) (mk vi S) steps (mk v' S'))
    (v : HS T Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ unaryIfLeSumCost n m W+budget ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(2*unaryIfLeSumCost n m W+reserve))
        depth (unaryIfLeSum a b band endpoint work tmp yes no) (mk v S) steps (mk v' S') := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec body (a := b) (b := endpoint) (t := tmp)
    ‹b ≠ endpoint› ‹b ≠ tmp› ‹endpoint ≠ tmp› v S (hfresh tmp (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R endpoint (List.replicate m tick)}
  have he₁' : Exec body (ucopy b endpoint tmp) (mk v S) (4*m+4) (mk v₁ S₁) := by
    simpa [S₁,hm,hfresh endpoint (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := band) (b := endpoint) (t := tmp)
    ‹band ≠ endpoint› ‹band ≠ tmp› ‹endpoint ≠ tmp› v₁ S₁ (by
      simpa [S₁,‹endpoint ≠ tmp›.symm] using hfresh tmp (by simp))
  let S₂ : Stacks T A := {S with R := Function.update S.R endpoint (List.replicate (m+W) tick)}
  have he₂' : Exec body (ucopy band endpoint tmp) (mk v₁ S₁) (4*W+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hW,‹band ≠ endpoint›,List.replicate_append_replicate,Nat.add_comm] using he₂
  let S₃ : Stacks T A := {S with R := Function.update S.R endpoint (List.replicate (m+W+1) tick)}
  have he₃ : Exec body (.act (.push (.rt endpoint) (fun _ => tick) .done)) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    simpa [S₃,S₂,Action.run,update_rt,List.replicate_succ] using
      Exec.act (body := body) (.push (.rt endpoint) (fun _ => tick) .done) (mk v₂ S₂)
  have hinner : ∀ vi : HS T Q A U, ∃ v' steps, v'.user = vi.user ∧ steps ≤ (2*(m+W+1)+2)+budget ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi S₃)+depth+reserve)
        depth (if n < m+W+1 then .seq (uclear endpoint) yes else .seq (uclear endpoint) no)
        (mk vi S₃) steps (mk v' S') := by
    intro vi
    obtain ⟨vc,huc,hec⟩ := uclear_exec body endpoint vi S₃
    have hec' : Exec body (uclear endpoint) (mk vi S₃) (2*(m+W+1)+2) (mk vc S) := by
      convert hec using 1
      · simp [S₃]
      · apply congrArg (mk vc)
        refine Stacks.ext rfl rfl rfl ?_
        funext k
        by_cases hk : k = endpoint <;> simp_all [S₃,hfresh endpoint (by simp)]
    obtain ⟨v',steps,hu,hs,he⟩ := hbranch vc
    have hstock : mnSize (mk vc S) ≤ mnSize (mk vi S₃) := by
      have h := mn_size_update (mk vc S) vi (.rt endpoint) (List.replicate (m+W+1) tick)
      have h' : mnSize (mk vi S₃)+(S.R endpoint).length = mnSize (mk vc S)+(m+W+1) := by
        simpa only [S₃,mk,update_rt,get_rt,List.length_replicate] using h
      rw [hfresh endpoint (by simp),List.length_nil] at h'
      omega
    have hc := mn_native_exec_within hec' 0 (by
      simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth
      (mnSize (mk vi S₃)+depth+reserve) (by omega)
    have hb := he.mono (J := fun d z => mnSize z+d ≤ mnSize (mk vi S₃)+depth+reserve)
      (by intro d z hz; omega)
    refine ⟨v',(2*(m+W+1)+2)+steps,hu.trans huc,Nat.add_le_add_left hs _,?_⟩
    by_cases h : n ≤ m+W
    · have hlt : n < m+W+1 := by omega
      simpa only [h,hlt,ite_true] using ExecWithin.seq hc hb
    · have hlt : ¬n < m+W+1 := by omega
      simpa only [h,hlt,ite_false] using ExecWithin.seq hc hb
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := unaryIfLt_exec_within (body := body)
    (a := a) (b := endpoint) (work := work) (tmp := tmp) (by regs_nodup)
    (.seq (uclear endpoint) yes) (.seq (uclear endpoint) no) n (m+W+1) ((2*(m+W+1)+2)+budget) reserve depth S₃ S'
    (by simpa [S₃,‹a ≠ endpoint›] using hn) (by simp [S₃])
    (by simpa [S₃,‹endpoint ≠ work›.symm] using hfresh work (by simp))
    (by simpa [S₃,‹endpoint ≠ tmp›.symm] using hfresh tmp (by simp)) hinner v₂
  have hcopy (src : Fin T) : mnNativePushBound 2
      (ucopy (P := P) (Q := Q) (A := A) (U := U) src endpoint tmp) := by
    simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have ht₁ := mn_native_exec_within he₁' 2 (hcopy b) depth _ (Nat.le_refl _)
  have ht₂ := mn_native_exec_within he₂' 2 (hcopy band) depth _ (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃ 1 (by simp [mnNativePushBound,mnActPush]) depth _ (Nat.le_refl _)
  have ht := (mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (mn_seq_within_add ht₃ he₄))).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(2*unaryIfLeSumCost n m W+reserve)) (by
      intro d z hz
      dsimp only [unaryIfLeSumCost]
      omega)
  refine ⟨v₄,(4*m+4)+((4*W+4)+(1+m₄)),hu₄.trans (hu₂.trans hu₁),by dsimp [unaryIfLeSumCost]; omega,
    ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
