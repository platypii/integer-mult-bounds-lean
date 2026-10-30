module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverCall
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorFinish

/-! Descriptor steps for solvers which may change their entire private bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast

variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- The exact cleanup bill of a final private bank. -/
def descriptorBankCleanupCost (output : Fin N) (F : Stacks N A) : ℕ :=
  4 * (F.R output).length + 2 * (∑ i, (F.R i).length) +
    4 * (∑ i, (F.L i).length) + 6 * N + 6

/-- Collect the output while emptying both sides of the private bank.
The solver's input and output tapes remain explicit in this state. -/
def finishedDescriptorBankState (work : Fin N → Fin T) (output : Fin N)
    (result : Fin T) (F : Stacks N A) (B : Stacks T A) : Stacks T A :=
  {embOvr work F.get B with
    L := fun k => if k ∈ List.ofFn work then [] else B.L k
    R := fun k => if k ∈ List.ofFn work then [] else
      if k = result then F.R output ++ B.R result else B.R k}

/-- A solver which preserves the host tapes returns the original empty-bank
frame, with only its published word prepended to the result register. -/
theorem finishedDescriptorBankState_eq
    (work : Fin N → Fin T) (output : Fin N) (result : Fin T)
    (F : Stacks N A) (B : Stacks T A)
    (hinp : F.inp = B.inp) (hout : F.out = B.out)
    (hleft : ∀ i, B.L (work i) = []) (hright : ∀ i, B.R (work i) = [])
    (hresult : ∀ i, work i ≠ result) :
    finishedDescriptorBankState work output result F B =
      {B with R := Function.update B.R result (F.R output ++ B.R result)} := by
  refine Stacks.ext hinp hout ?_ ?_
  · funext k
    change (if k ∈ List.ofFn work then [] else B.L k) = B.L k
    by_cases hk : k ∈ List.ofFn work
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      rw [ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩), hleft i]
    · rw [ite_eq_right hk]
  · funext k
    change (if k ∈ List.ofFn work then [] else
      if k = result then F.R output ++ B.R result else B.R k) =
      Function.update B.R result (F.R output ++ B.R result) k
    by_cases hk : k ∈ List.ofFn work
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      rw [ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩), Function.update_of_ne (hresult i), hright i]
    · rw [ite_eq_right hk]
      by_cases hkr : k = result
      · subst k; simp
      · simp [hkr]

theorem finishEmbeddedDescriptorBank_exec
    (work : Fin N → Fin T) (hwork : Function.Injective work)
    (output : Fin N) (result tmp : Fin T) (hrt : result ≠ tmp)
    (hresult : ∀ i, work i ≠ result) (htmp : ∀ i, work i ≠ tmp)
    (v : HS T Q A U) (F : Stacks N A) (B : Stacks T A) (hblank : B.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ descriptorBankCleanupCost output F ∧
      Exec body (finishDescriptorBankBoth (List.ofFn work) (work output) result tmp)
        (mk v (embOvr work F.get B)) n
        (mk v' (finishedDescriptorBankState work output result F B)) := by
  have hgetR (i : Fin N) : (embOvr work F.get B).R (work i) = F.R i :=
    by simp only [embOvr, Stacks.get, embExt_apply hwork]
  have hgetL (i : Fin N) : (embOvr work F.get B).L (work i) = F.L i :=
    by simp only [embOvr, Stacks.get, embExt_apply hwork]
  have hoff (k : Fin T) (hk : k ∉ List.ofFn work) :
      (embOvr work F.get B).L k = B.L k ∧ (embOvr work F.get B).R k = B.R k := by
    apply embOvr_off
    intro i hi
    exact hk (List.mem_ofFn.mpr ⟨i, hi⟩)
  have hr : result ∉ List.ofFn work := by
    intro h; obtain ⟨i, hi⟩ := List.mem_ofFn.mp h; exact hresult i hi
  have ht : tmp ∉ List.ofFn work := by
    intro h; obtain ⟨i, hi⟩ := List.mem_ofFn.mp h; exact htmp i hi
  obtain ⟨v', n, hu, hn, he⟩ := finishDescriptorBankBoth_exec (body := body)
    (List.ofFn work) (List.nodup_ofFn.mpr hwork) (work output) result tmp
    (List.mem_ofFn.mpr ⟨output, rfl⟩) hr ht hrt v (embOvr work F.get B)
    ((hoff tmp ht).2.trans hblank)
  refine ⟨v', n, hu, ?_, he.cast rfl ?_⟩
  · simpa only [List.map_ofFn, Function.comp_def, List.sum_ofFn, List.length_ofFn,
      hgetR, hgetL, descriptorBankCleanupCost] using hn
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl ?_ ?_
    · funext k
      by_cases hk : k ∈ List.ofFn work
      · simp only [finishedDescriptorBankState, hk, ite_true]
      · simp only [finishedDescriptorBankState, hk, ite_false, (hoff k hk).1]
    · funext k
      by_cases hk : k ∈ List.ofFn work
      · simp only [finishedDescriptorBankState, hk, ite_true]
      · simp only [finishedDescriptorBankState, hk, ite_false, (hoff k hk).2, hgetR, (hoff result hr).2]

/-- After descriptor loading, cleanup restores the caller's original bank.
Only the descriptor cursors and accumulated output remain changed. -/
theorem finishedPlacedDescriptorBankState_eq
    (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4)))
    (src saved result : Fin T) (output : Fin N) (rest : List (Fin (A+4)))
    (F : Stacks N A) (S : Stacks T A)
    (hinp : F.inp = S.inp) (hout : F.out = S.out)
    (hleft : ∀ i, S.L (work i) = []) (hright : ∀ i, S.R (work i) = [])
    (hreg : [src,saved,result].Nodup) (hsep : ∀ i, work i ∉ [src,saved,result]) :
    finishedDescriptorBankState work output result F
      (placedDescriptorState work words src saved rest S) =
      dispatchedDescriptorState work words src saved result rest (F.R output) S := by
  have hr := hreg
  regs_ne hr
  have hn (i : Fin N) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ result := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hsep i
  refine Stacks.ext hinp hout ?_ ?_
  · funext k
    change (if k ∈ List.ofFn work then [] else S.L k) = S.L k
    by_cases hk : k ∈ List.ofFn work
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      rw [ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩), hleft i]
    · rw [ite_eq_right hk]
  · funext k
    by_cases hk : k ∈ List.ofFn work
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hk
      simp only [finishedDescriptorBankState, List.mem_ofFn.mpr ⟨i, rfl⟩, ite_true,
        dispatchedDescriptorState, Function.update_of_ne (hn i).1,
        Function.update_of_ne (hn i).2.1, Function.update_of_ne (hn i).2.2, hright i]
    · have hwork (i : Fin N) : work i ≠ k := by
        intro he; exact hk (List.mem_ofFn.mpr ⟨i, he⟩)
      have hf : (placedDescriptorState work words src saved rest S).R result = S.R result :=
        placedDescriptorState_frame work words src saved rest S result
          (fun i => (hn i).2.2) ‹src ≠ result›.symm ‹saved ≠ result›.symm
      simp only [finishedDescriptorBankState, hk, ite_false, hf, dispatchedDescriptorState]
      by_cases hkr : k = result
      · subst k; simp
      · rw [ite_eq_right hkr, Function.update_of_ne hkr]
        by_cases hks : k = src
        · subst k; simp [placedDescriptorState, ‹src ≠ saved›]
        · by_cases hkv : k = saved
          · subst k; simp [placedDescriptorState]
          · rw [placedDescriptorState_frame work words src saved rest S k hwork hks hkv,
              Function.update_of_ne hkv, Function.update_of_ne hks]

def descriptorBankStep (work : Fin N → Fin T) (src saved count tmp spare result : Fin T)
    (output : Fin N) (solve : Pr Empty N Q A U) : Pr P T Q A U :=
  .seq (descriptorSolverCall work src saved count tmp spare solve)
    (finishDescriptorBankBoth (List.ofFn work) (work output) result tmp)

/-- Compose loading, an arbitrary private-bank solver, and actual cleanup.
Readiness and solver resource certificates are premises, not supplied by placement. -/
theorem descriptorBankStep_exec
    (work : Fin N → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (hresult : ∀ i, work i ≠ result) (hrt : result ≠ tmp)
    (words : Fin N → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (output : Fin N) (solve : Pr Empty N Q A U) (time stock cleanup : ℕ)
    (post : Stacks N A → Prop) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words) ++ rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS N Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n (mk vf F) ∧ post F ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n (mk vf F))
    (hcleanup : ∀ F, post F → descriptorBankCleanupCost output F ≤ cleanup) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ takeDescriptorBankCost (placedDescriptorFields work words) + time + cleanup ∧
      Exec body (descriptorBankStep work src saved count tmp spare result output solve) (mk v S) n
        (mk v' (finishedDescriptorBankState work output result F
          (placedDescriptorState work words src saved rest S))) ∧ post F ∧
      ∀ C, mnProgPush (descriptorBankStep (P := P) work src saved count tmp spare result output solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock+cleanup)) depth
          (descriptorBankStep work src saved count tmp spare result output solve) (mk v S) n
          (mk v' (finishedDescriptorBankState work output result F
            (placedDescriptorState work words src saved rest S))) := by
  obtain ⟨v₁, F, n₁, hu₁, hn₁, he₁, hp, ht⟩ := descriptorSolverCall_exec_bank (body := body)
    work hwork src saved count tmp spare hreg hsep words rest solve time stock post v S
    hblank hsource hcount htmp hspare hsolve
  have hr := hreg
  regs_ne hr
  have htmpWork (i : Fin N) : work i ≠ tmp := by
    have hi := hsep i
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    exact hi.2.2.2.1
  have hb : (placedDescriptorState work words src saved rest S).R tmp = [] := by
    rw [placedDescriptorState_frame work words src saved rest S tmp htmpWork
      ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm, htmp]
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := finishEmbeddedDescriptorBank_exec (body := body)
    work hwork output result tmp hrt hresult htmpWork v₁ F
    (placedDescriptorState work words src saved rest S) hb
  have hn₂' := hn₂.trans (hcleanup F hp)
  exact ⟨v₂, F, n₁+n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂',
    Exec.seq he₁ he₂, hp, mn_seq_exec_within ht (mn_bounded_exec_certify he₂ hn₂')⟩

/-- A ready solver with a host-tape frame supplies the exact restoring-schedule endpoint. -/
theorem descriptorBankStep_exec_restored
    (work : Fin N → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare])
    (hresult : ∀ i, work i ≠ result) (hrt : result ≠ tmp)
    (houter : [src,saved,result].Nodup)
    (words : Fin N → List (Fin (A+4))) (rest : List (Fin (A+4)))
    (output : Fin N) (solve : Pr Empty N Q A U) (time stock cleanup : ℕ)
    (post : Stacks N A → Prop) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work words) ++ rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = [])
    (hsolve : ∀ vi : HS N Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n (mk vf F) ∧ post F ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n (mk vf F))
    (hcleanup : ∀ F, post F → descriptorBankCleanupCost output F ≤ cleanup)
    (hhost : ∀ F, post F → F.inp = S.inp ∧ F.out = S.out) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ takeDescriptorBankCost (placedDescriptorFields work words) + time + cleanup ∧
      Exec body (descriptorBankStep work src saved count tmp spare result output solve) (mk v S) n
        (mk v' (dispatchedDescriptorState work words src saved result rest (F.R output) S)) ∧ post F ∧
      ∀ C, mnProgPush (descriptorBankStep (P := P) work src saved count tmp spare result output solve) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock+cleanup)) depth
          (descriptorBankStep work src saved count tmp spare result output solve) (mk v S) n
          (mk v' (dispatchedDescriptorState work words src saved result rest (F.R output) S)) := by
  obtain ⟨v', F, n, hu, hn, he, hp, ht⟩ := descriptorBankStep_exec (body := body)
    work hwork src saved count tmp spare result hreg hsep hresult hrt words rest output
    solve time stock cleanup post v S hblank hsource hcount htmp hspare hsolve hcleanup
  have hsep' (i : Fin N) : work i ∉ [src,saved,result] := by
    have hi := hsep i
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi ⊢
    exact ⟨hi.1, hi.2.1, hresult i⟩
  have hf := finishedPlacedDescriptorBankState_eq work words src saved result output rest F S
    (hhost F hp).1 (hhost F hp).2 hleft hblank houter hsep'
  rw [hf] at he ht
  exact ⟨v', F, n, hu, hn, he, hp, ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
