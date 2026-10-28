module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! Execute the descriptor schedule and restore its tape, count and private workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def familyDispatch (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (copyR clock savedClock tmp id)
    (.seq (familyDispatchLoop work src saved count tmp spare result clock recovery hR hQ)
      (.seq (moveR saved src id) (moveR savedClock clock id)))

theorem familyDispatch_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
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
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (records.map (fun r => r.cost p l t work+3)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 ∧
      Exec body (familyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs := by
  have hsub : [src,saved,count,tmp,spare,result,clock].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or] at hreg ⊢
    tauto
  have hr := hreg
  regs_ne hr
  have hn (i : Fin 303) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧ work i ≠ tmp ∧
      work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock ∧ work i ≠ savedClock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  have htmp : S.R tmp = [] := hscratch tmp (by simp)
  obtain ⟨v₀,hu₀,he₀⟩ := copyR_exec (body := body) clock savedClock tmp
    ‹clock ≠ savedClock› ‹tmp ≠ clock›.symm ‹tmp ≠ savedClock›.symm id v S htmp
  simp only [List.map_id] at he₀
  let S₀ : Stacks T A := {S with R := Function.update S.R savedClock ((S.R clock).reverse++S.R savedClock)}
  obtain ⟨v₁,n₁,outputs,hu₁,hn₁,he₁,hgood⟩ := familyDispatchLoop_exec (body := body)
    work hwork src saved count tmp spare result clock hsub
    (by intro i; simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨(hn i).1,(hn i).2.1,(hn i).2.2.1,(hn i).2.2.2.1,
          (hn i).2.2.2.2.1,(hn i).2.2.2.2.2.1,(hn i).2.2.2.2.2.2.1⟩)
    recovery hR hQ hA hp hst hθ hgap records hready x y hx hy v₀ S₀ rest
    (by intro i; simpa only [S₀,Function.update_of_ne (hn i).2.2.2.2.2.2.2] using hblank i)
    hleft
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with hk | hk | hk
        · subst k; simpa only [S₀,Function.update_of_ne ‹count ≠ savedClock›] using hscratch count (by simp)
        · subst k; simpa only [S₀,Function.update_of_ne ‹tmp ≠ savedClock›] using htmp
        · subst k; simpa only [S₀,Function.update_of_ne ‹spare ≠ savedClock›] using hscratch spare (by simp))
    (by simpa only [S₀,Function.update_of_ne ‹src ≠ savedClock›] using hsource)
    (by simpa only [S₀,Function.update_of_ne ‹clock ≠ savedClock›] using hclock)
  let tape := descriptorScheduleTape work FamilyDispatchInput.words records
  let S₁ := descriptorLoopFinal work FamilyDispatchInput.words records src saved result clock rest outputs S₀
  have hs₁ : S₁.R saved = tape.reverse := by
    simp only [S₁,descriptorLoopFinal,Function.update_of_ne ‹saved ≠ clock›,
      Function.update_of_ne ‹saved ≠ result›,Function.update_self,S₀,
      Function.update_of_ne ‹saved ≠ savedClock›,hsaved,List.append_nil,tape]
  obtain ⟨v₂,hu₂,he₂⟩ := restoreDescriptorTape_exec (body := body) src saved ‹src ≠ saved›.symm v₁ S₁ tape hs₁
  let S₂ : Stacks T A := {S₁ with R := Function.update (Function.update S₁.R saved []) src (tape++S₁.R src)}
  have hsc₂ : S₂.R savedClock = (S.R clock).reverse := by
    simp only [S₂,Function.update_of_ne ‹src ≠ savedClock›.symm,Function.update_of_ne ‹saved ≠ savedClock›.symm,
      S₁,descriptorLoopFinal,Function.update_of_ne ‹clock ≠ savedClock›.symm,
      Function.update_of_ne ‹result ≠ savedClock›.symm,S₀,Function.update_self,hsavedClock,List.append_nil]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec body savedClock clock ‹clock ≠ savedClock›.symm id v₂ S₂
  have hfinal : ({S₂ with R := movedR S₂.R savedClock clock id (S₂.R savedClock)} : Stacks T A) =
      {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [movedR,hsc₂,List.map_id,List.reverse_reverse,S₂,S₁,descriptorLoopFinal,S₀,
      Function.update_apply,hsaved,hsavedClock,List.append_nil]
    split_ifs <;> subst_vars <;> simp_all only [List.append_assoc,Ne.symm,ne_self_iff_false,List.reverse_reverse,List.append_nil,tape]
  refine ⟨v₃,(4*(S.R clock).length+4)+(n₁+((2*tape.length+2)+(2*(S₂.R savedClock).length+2))),
    outputs,hu₃.trans (hu₂.trans (hu₁.trans hu₀)),?_,
    (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃))).cast rfl (congrArg (mk v₃) hfinal),hgood⟩
  rw [hclock,hsc₂,List.length_reverse]
  dsimp only [tape]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
