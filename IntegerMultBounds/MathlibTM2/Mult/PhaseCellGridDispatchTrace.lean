module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedDispatchProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorSolverSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! The complete restored numerical dispatch carries an execution-wide stock certificate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def gridFamilyDispatch (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  descriptorSolverSchedule src saved tmp clock savedClock
    (gridFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)

theorem gridFamilyDispatch_exec_trace (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} {d : ℝ} (hp : 2 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A)) (hready : ∀ r ∈ records, GridDispatchReady p l t d r)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work FamilyDispatchInput.words records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => r.gridCost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 ∧
      Exec body (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ (NormalizedDispatchProduced p x y) records outputs ∧
      ∀ C, mnProgPush (gridFamilyDispatch work src saved count tmp spare result clock savedClock
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map (fun r => r.gridStock p l t work)).sum+6*records.length+
            2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8))
          depth (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
          (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  have hsub : [src,saved,count,tmp,spare].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hr := hreg
  regs_ne hr
  have hresult : result ∉ [src,saved,count,tmp,spare] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨‹src ≠ result›.symm,‹saved ≠ result›.symm,‹count ≠ result›.symm,
      ‹tmp ≠ result›.symm,‹spare ≠ result›.symm⟩
  have hn (i : Fin 303) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧ work i ≠ tmp ∧
      work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock ∧ work i ≠ savedClock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  apply descriptorSolverSchedule_exec_trace work hwork src saved count tmp spare result clock savedClock hreg hsep
    FamilyDispatchInput.words (gridFamilyInverseBatchDispatchStep work src saved count tmp spare result recovery hR hQ)
    (fun r => r.gridCost p l t work) (fun r => r.gridStock p l t work) (NormalizedDispatchProduced p x y)
    records v S ?_ rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  intro r hm vi Si tail hb hl hs hc ht hsp
  obtain ⟨vf,n,Zs,hu,hnTime,he,ha,htrace⟩ := gridDispatchInput_exec (body := body) work hwork
    src saved count tmp spare result hsub hresult (fun i => (hn i).2.2.2.2.2.1)
    (by intro i; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.1,(hn i).2.2.2.1,(hn i).2.2.2.2.1⟩)
    recovery hR hQ hA hp hst hθ hgap r (hready r hm) (x r) (y r) (hx r hm) (hy r hm)
    vi Si tail hb hl hs hc ht hsp
  exact ⟨vf,n,r.normalizedOutput p Zs,hu,hnTime,he,⟨Zs,rfl,ha⟩,htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
