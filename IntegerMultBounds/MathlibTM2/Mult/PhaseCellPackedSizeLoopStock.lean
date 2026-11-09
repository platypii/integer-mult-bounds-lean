module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSizeLoop
public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! Address construction shares one clipped-block controller reserve across the scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem packedSizeStep_native : mnNativePushBound 2
    (packedSizeStep (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [packedSizeStep,clippedBandControls,bandIntervalEndpoints,clipUnary,
    clearWords,ucopy,umulSym,usub,dropTop,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem packedSizeStepCost_le (start L W N i : ℕ) (hi : i < L) :
    packedSizeStepCost (start+i) W N ≤ 100*(start+L+W+N+1) := by
  unfold packedSizeStepCost clippedBandControlsCost bandIntervalEndpointsCost clipUnaryCost
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
  omega

theorem packedSizeLoop_exec_within (N W start L : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hN : (S.R 116).length = N) (hW : (S.R 94).length = W)
    (hcursor : (S.R 151).length = start) (hcount : (S.R 152).length = L)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,153], S.R k = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ packedSizeLoopCost N W start L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v' {S with R := (Function.update (Function.update S.R 0
          (List.replicate (packedBandWordCount N W L start) tick++S.R 0))
          151 (List.replicate L tick++S.R 151))})+depth+
        2*(100*(start+L+W+N+1)+2)) depth packedSizeLoop (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 0
          (List.replicate (packedBandWordCount N W L start) tick++S.R 0))
          151 (List.replicate L tick++S.R 151))}) := by
  let Ψ : ℕ → Regs 154 A := fun i => Function.update (Function.update S.R
    0 (List.replicate (packedBandWordCount N W i start) tick++S.R 0))
    151 (List.replicate i tick++S.R 151)
  have hstep : IterStockSpec body packedSizeStep 152 153 Ψ (100*(start+L+W+N+1)) L := by
    intro i hi vi Si hSi
    have hoff (k : Fin 154) (hk0 : k ≠ 0) (hk151 : k ≠ 151) (hk152 : k ≠ 152) (hk153 : k ≠ 153) :
        Si.R k = S.R k := by rw [hSi k hk152 hk153]; simp [Ψ,hk0,hk151]
    have hcursor' : (Si.R 151).length = start+i := by
      rw [hSi 151 (by decide) (by decide)]
      simp [Ψ,hcursor,Nat.add_comm]
    obtain ⟨vi',hu,he⟩ := packedSizeStep_exec (body := body) (start+i) W N vi Si hcursor'
      (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact hW)
      (by rw [hoff 116 (by decide) (by decide) (by decide) (by decide)]; exact hN) (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;>
          rw [hoff _ (by decide) (by decide) (by decide) (by decide)] <;> exact hfresh _ (by simp))
    let count := min N (start+i+W+1)-(start+i-W)
    let R' : Regs 154 A := Function.update (Function.update Si.R 0 (List.replicate count tick++Si.R 0))
      151 (tick::Si.R 151)
    refine ⟨vi',R',packedSizeStepCost (start+i) W N,hu,(packedSizeStepCost_le start L W N i hi),he,by simp [R'],by simp [R'],?_,?_⟩
    · intro k hk152 hk153
      by_cases hk0 : k = 0
      · subst k
        rw [show R' 0 = List.replicate count tick++Si.R 0 by simp [R'],hSi 0 (by decide) (by decide)]
        simp [Ψ,packedBandWordCount_succ,count,Nat.add_comm]
        rw [← List.append_assoc,List.replicate_append_replicate]
      by_cases hk151 : k = 151
      · subst k
        rw [show R' 151 = tick::Si.R 151 by simp [R'],hSi 151 (by decide) (by decide)]
        simp [Ψ,List.replicate_succ]
      rw [show R' k = Si.R k by simp [R',hk0,hk151],hSi k hk152 hk153]
      simp [Ψ,hk0,hk151]
    · let D : Stacks 154 A := {Si with R := Function.update Si.R 0 (List.replicate count tick++Si.R 0)}
      have h₁ : mnSize (mk vi D)+(Si.R 0).length =
          mnSize (mk vi Si)+(List.replicate count tick++Si.R 0).length := by
        simpa only [D,mk,update_rt,get_rt] using
          mn_size_update (mk vi Si) vi (.rt 0) (List.replicate count tick++Si.R 0)
      have h₂ : mnSize (mk vi' {D with R := Function.update D.R 151 (tick::Si.R 151)})+(D.R 151).length =
          mnSize (mk vi D)+(tick::Si.R 151).length := by
        simpa only [mk,update_rt,get_rt] using
          mn_size_update (mk vi D) vi' (.rt 151) (tick::Si.R 151)
      have h151 : D.R 151 = Si.R 151 := by simp [D]
      rw [h151,List.length_cons] at h₂
      simp only [List.length_append,List.length_replicate] at h₁
      change mnSize (mk vi Si) ≤ mnSize (mk vi' {D with R := Function.update D.R 151 (tick::Si.R 151)})
      omega
  obtain ⟨v',steps,hu,hm,he⟩ := packedSizeLoop_exec (body := body) N W start L v S hN hW hcursor hcount hfresh
  refine ⟨v',steps,hu,hm,?_⟩
  apply scanP_within_final_stock (by decide : (152 : Fin 154) ≠ 153)
    (by decide : 1 ≤ 2) packedSizeStep_native hstep 0 v S (by simp [hcount]) ?_ he depth
  intro k _ _
  by_cases hk0 : k = 0 <;> by_cases hk151 : k = 151 <;> simp [Ψ,packedBandWordCount,hk0,hk151]

theorem packedBandWordCount_le (N W L start : ℕ) :
    packedBandWordCount N W L start ≤ L*(2*W+1) := by
  induction L generalizing start with
  | zero => simp [packedBandWordCount]
  | succ L ih =>
    have hprev := ih (start+1)
    have hrow : min N (start+W+1)-(start-W) ≤ 2*W+1 := by omega
    change packedBandWordCount N W L (start+1)+_ ≤ _
    rw [Nat.add_mul,Nat.one_mul]
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
