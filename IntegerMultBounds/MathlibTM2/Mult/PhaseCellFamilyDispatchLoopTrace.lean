module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoopTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! The executed numerical descriptor loop carries every per-step stock certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem familyDispatchLoop_exec_trace (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} {d : ℝ} (hp : 2 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A)) (hready : ∀ r ∈ records, FamilyDispatchReady p l t d r)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => (value (r.precision p l t) (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => (value (r.precision p l t) (F i)).im))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work FamilyDispatchInput.words records++rest)
    (hclock : (S.R clock).length = records.length) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => r.cost p l t work+3)).sum+2 ∧
      Exec body (familyDispatchLoop work src saved count tmp spare result clock recovery hR hQ)
        (mk v S) n (mk v' (descriptorLoopFinal work FamilyDispatchInput.words records src saved result clock rest outputs S)) ∧
      List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs ∧
      ∀ C, mnProgPush (familyDispatchLoop work src saved count tmp spare result clock
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(records.map (fun r => r.stock p l t work)).sum)
          depth (familyDispatchLoop work src saved count tmp spare result clock recovery hR hQ)
          (mk v S) n (mk v' (descriptorLoopFinal work FamilyDispatchInput.words records src saved result clock rest outputs S)) := by
  have hsub : [src,saved,count,tmp,spare].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have houter : [src,saved,result,clock].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hr := hreg
  regs_ne hr
  have hresult : result ∉ [src,saved,count,tmp,spare] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨‹src ≠ result›.symm,‹saved ≠ result›.symm,‹count ≠ result›.symm,
      ‹tmp ≠ result›.symm,‹spare ≠ result›.symm⟩
  have hn (i : Fin 303) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧
      work i ≠ tmp ∧ work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  let fresh := List.ofFn work ++ [count,tmp,spare]
  have hcontrol : ∀ k ∈ [count,tmp,spare], k ∉ [src,saved,result,clock] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with hk | hk | hk
    · subst k
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨‹src ≠ count›.symm,‹saved ≠ count›.symm,‹count ≠ result›,‹count ≠ clock›⟩
    · subst k
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨‹src ≠ tmp›.symm,‹saved ≠ tmp›.symm,‹tmp ≠ result›,‹tmp ≠ clock›⟩
    · subst k
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨‹src ≠ spare›.symm,‹saved ≠ spare›.symm,‹spare ≠ result›,‹spare ≠ clock›⟩
  have hfresh : ∀ k ∈ fresh, k ∉ [src,saved,result,clock] := by
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.2.2.2.1,(hn i).2.2.2.2.2.2⟩
    · exact hcontrol k hk
  have hcountFresh : count ∈ fresh := List.mem_append_right _ (by simp)
  have htmpFresh : tmp ∈ fresh := List.mem_append_right _ (by simp)
  have hspareFresh : spare ∈ fresh := List.mem_append_right _ (by simp)
  apply descriptorListLoop_exec_trace work FamilyDispatchInput.words src saved result clock houter fresh hfresh S.L
    (familyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
    (fun r => r.cost p l t work) (fun r => r.stock p l t work) (FamilyDispatchProduced p l t x y) records ?_ v S rest ?_ rfl hsource hclock
  · intro r hm vi Si tail hf hL hs
    obtain ⟨vf,n,Zs,hu,hnTime,he,ha,ht⟩ := familyDispatchInput_exec (body := body) work hwork
      src saved count tmp spare result hsub hresult (fun i => (hn i).2.2.2.2.2.1)
      (by intro i; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.1,(hn i).2.2.2.1,(hn i).2.2.2.2.1⟩)
      recovery hR hQ hA hp hst hθ hgap r (hready r hm) (x r) (y r) (hx r hm) (hy r hm)
      vi Si tail (fun i => hf (work i) (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))
      (by intro i; rw [hL]; exact hleft i) hs
      (hf count hcountFresh) (hf tmp htmpFresh) (hf spare hspareFresh)
    exact ⟨vf,n,r.output p l t Zs,hu,hnTime,he,⟨Zs,rfl,ha⟩,ht⟩
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
      exact hblank i
    · exact hscratch k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
