module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedDescriptorBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBankFinish

/-! Collect the produced word and return the placed bank to its original empty frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem placedDescriptorState_work (work : Fin N → Fin T) (hwork : Function.Injective work)
    (words : Fin N → List (Fin (A+4))) (src saved : Fin T) (rest : List (Fin (A+4)))
    (S : Stacks T A) (hblank : ∀ i, S.R (work i) = [])
    (hsep : ∀ i, work i ≠ src ∧ work i ≠ saved) (i : Fin N) :
    (placedDescriptorState work words src saved rest S).R (work i) = words i := by
  simp only [placedDescriptorState,Function.update_of_ne (hsep i).2,Function.update_of_ne (hsep i).1]
  simpa only [placedDescriptorFields,hblank,List.append_nil] using descriptorBankR_ofFn work hwork words S.R i

theorem placedDescriptorState_frame (work : Fin N → Fin T)
    (words : Fin N → List (Fin (A+4))) (src saved : Fin T) (rest : List (Fin (A+4)))
    (S : Stacks T A) (k : Fin T) (hwork : ∀ i, work i ≠ k) (hs : k ≠ src) (hv : k ≠ saved) :
    (placedDescriptorState work words src saved rest S).R k = S.R k := by
  simp only [placedDescriptorState,Function.update_of_ne hv,Function.update_of_ne hs]
  apply descriptorBankR_frame
  intro f hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  exact hwork i

def dispatchedDescriptorState (work : Fin N → Fin T) (words : Fin N → List (Fin (A+4)))
    (src saved result : Fin T) (rest produced : List (Fin (A+4))) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R src rest)
    saved ((descriptorBankTape (placedDescriptorFields work words)).reverse++S.R saved))
    result (produced++S.R result))}

theorem finishPlacedDescriptorBank_exec (work : Fin N → Fin T) (hwork : Function.Injective work)
    (words : Fin N → List (Fin (A+4))) (src saved result tmp : Fin T)
    (hreg : [src,saved,result,tmp].Nodup) (hsep : ∀ i, work i ∉ [src,saved,result,tmp])
    (output : Fin N) (rest produced : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ i, S.R (work i) = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 6*produced.length+2*(∑ i, (words i).length)+2*N+5 ∧
      Exec body (finishDescriptorBank (List.ofFn work) (work output) result tmp)
        (mk v {placedDescriptorState work words src saved rest S with R :=
          (Function.update (placedDescriptorState work words src saved rest S).R (work output) produced)}) n
        (mk v' (dispatchedDescriptorState work words src saved result rest produced S)) := by
  have hr := hreg
  regs_ne hr
  have hne (i : Fin N) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ result ∧ work i ≠ tmp := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  let S₁ := placedDescriptorState work words src saved rest S
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R (work output) produced}
  have hw (i : Fin N) : S₁.R (work i) = words i :=
    placedDescriptorState_work work hwork words src saved rest S hblank (fun i => ⟨(hne i).1,(hne i).2.1⟩) i
  have hf (k : Fin T) (hk : ∀ i, work i ≠ k) (hs : k ≠ src) (hv : k ≠ saved) : S₁.R k = S.R k :=
    placedDescriptorState_frame work words src saved rest S k hk hs hv
  have hresult : result ∉ List.ofFn work := by
    intro hm; obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm; exact (hne i).2.2.1 hi
  have htmpPorts : tmp ∉ List.ofFn work := by
    intro hm; obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm; exact (hne i).2.2.2 hi
  have ht : S₂.R tmp = [] := by
    dsimp only [S₂]
    rw [Function.update_of_ne (hne output).2.2.2.symm,hf tmp (fun i => (hne i).2.2.2)
      ‹src ≠ tmp›.symm ‹saved ≠ tmp›.symm,htmp]
  obtain ⟨v',n,hu,hn,he⟩ := finishDescriptorBank_exec (body := body) (List.ofFn work)
    (List.nodup_ofFn.mpr hwork) (work output) result tmp (List.mem_ofFn.mpr ⟨output,rfl⟩)
    hresult htmpPorts ‹result ≠ tmp› v S₂ ht
  have hsum : ((List.ofFn work).map (fun k => (S₂.R k).length)).sum ≤
      (∑ i, (words i).length)+produced.length := by
    simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn]
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (S₂.R (work i)).length ≤ (words i).length+(if i = output then produced.length else 0) from by
        by_cases hi : i = output
        · subst i; simp [S₂]
        · simp [S₂,hwork.ne hi,hw,hi])
    simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  refine ⟨v',n,hu,?_,he.cast rfl ?_⟩
  · have hout : S₂.R (work output) = produced := Function.update_self _ _ _
    rw [hout,List.length_ofFn] at hn
    omega
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ List.ofFn work
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      simp [dispatchedDescriptorState,hne,hblank]
    · have hkw : ∀ i, work i ≠ k := by
        intro i hi; exact hk (List.mem_ofFn.mpr ⟨i,hi⟩)
      have hko : k ≠ work output := (hkw output).symm
      by_cases hkr : k = result
      · subst k
        simp [S₂,hresult,hko,hf result (fun i => (hne i).2.2.1)
          ‹src ≠ result›.symm ‹saved ≠ result›.symm,dispatchedDescriptorState]
      · simp only [hk,ite_false,hkr,S₂,Function.update_of_ne hko,
          dispatchedDescriptorState,Function.update_of_ne hkr]
        by_cases hks : k = src
        · subst k; simp [S₁,placedDescriptorState,‹src ≠ saved›]
        · by_cases hkv : k = saved
          · subst k; simp [S₁,placedDescriptorState]
          · simp [hf k hkw hks hkv,hks,hkv]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
