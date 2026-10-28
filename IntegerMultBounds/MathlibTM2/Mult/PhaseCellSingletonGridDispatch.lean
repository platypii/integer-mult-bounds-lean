module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonGridRecord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchTrace

/-! A singleton descriptor executes the actual restored production dispatcher. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def singletonGridDispatchState {s : ℕ} [NeZero s] (work : Fin 303 → Fin T)
    (src clock : Fin T) (p u l target t : ℕ) (F : ZMod s → GaussianInt) (S : Stacks T A) : Stacks T A :=
  {S with R := Function.update (Function.update S.R src
    (descriptorScheduleTape work FamilyDispatchInput.words [singletonGridRecord p u l target t F])) clock [Node.tick]}

theorem singletonGridDispatch_exec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value p (F i)‖ ≤ 1)
    (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hcontrol : ∀ k ∈ [count,tmp,spare,result,saved,savedClock], S.R k = [])
    (yr yi : ZMod s → ℝ)
    (hyr : Matrix.mulVec (realMatrix s t p u) yr = (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hyi : Matrix.mulVec (realMatrix s t p u) yi = (fun i => ((1/2 : ℂ)*value p (F i)).im)) :
    let r := singletonGridRecord (A := A) p u l target t F
    let initial := singletonGridDispatchState work src clock p u l target t F S
    ∃ v' n G, v'.user = v.user ∧
      n ≤ r.gridCost p l t work+2*(descriptorScheduleTape work FamilyDispatchInput.words [r]).length+19 ∧
      Exec body (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v initial) n (mk v' {initial with R := Function.update initial.R result (cstream A (2*p+13) (chirpLine s G))}) ∧
      ∀ i, ‖pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s G)) i-
        ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨yr i,yi i⟩ : ℂ)‖ ≤
          2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p := by
  dsimp only
  let r := singletonGridRecord (A := A) p u l target t F
  let initial := singletonGridDispatchState work src clock p u l target t F S
  have hr := hreg
  regs_ne hr
  have hf (k : Fin T) (hs : k ≠ src) (hc : k ≠ clock) : initial.R k = S.R k := by
    simp only [initial,singletonGridDispatchState,Function.update_of_ne hs,Function.update_of_ne hc]
  have hn (i : Fin 303) : work i ≠ src ∧ work i ≠ saved ∧ work i ≠ count ∧ work i ≠ tmp ∧
      work i ≠ spare ∧ work i ≠ result ∧ work i ≠ clock ∧ work i ≠ savedClock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  have hready : GridDispatchReady p l t d r := singletonGridRecord_ready p u l target t hu hwidth
    (by rw [←hαu]; exact hbudget) hband hpad F hF
  have hx : Solves (realMatrix s t p u) (haloVertices s 0 s) yr
      (fun i => ((1/2 : ℂ)*value p (F i)).re) := by
    rw [haloVertices_full]
    intro i _
    exact congrFun hyr i
  have hy : Solves (realMatrix s t p u) (haloVertices s 0 s) yi
      (fun i => ((1/2 : ℂ)*value p (F i)).im) := by
    rw [haloVertices_full]
    intro i _
    exact congrFun hyi i
  obtain ⟨v',n,outputs,huser,hcost,he,herror,_⟩ := gridFamilyDispatch_exec_trace (body := body)
    work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA hp hst hθ hgap
    [r] (by intro r' hm; simpa only [List.mem_singleton.mp hm] using hready)
    (fun _ _ => yr) (fun _ _ => yi)
    (by intro r' hm G hG; have he := List.mem_singleton.mp hm; subst r'
        have heF : G = F := List.mem_singleton.mp hG; subst G; exact hx)
    (by intro r' hm G hG; have he := List.mem_singleton.mp hm; subst r'
        have heF : G = F := List.mem_singleton.mp hG; subst G; exact hy)
    v initial [] (fun i => (hf (work i) (hn i).1 (hn i).2.2.2.2.2.2.1).trans (hblank i)) hleft
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with hk|hk|hk
        · subst k
          exact (hf count ‹src ≠ count›.symm ‹count ≠ clock›).trans (hcontrol count (by simp))
        · subst k
          exact (hf tmp ‹src ≠ tmp›.symm ‹tmp ≠ clock›).trans (hcontrol tmp (by simp))
        · subst k
          exact (hf spare ‹src ≠ spare›.symm ‹spare ≠ clock›).trans (hcontrol spare (by simp)))
    (by simp only [initial,singletonGridDispatchState,Function.update_of_ne ‹src ≠ clock›,Function.update_self,List.append_nil]
        rfl)
    (by simp only [initial,singletonGridDispatchState,Function.update_self,List.length_cons,List.length_nil])
    ((hf saved ‹src ≠ saved›.symm ‹saved ≠ clock›).trans (hcontrol saved (by simp)))
    ((hf savedClock ‹src ≠ savedClock›.symm ‹clock ≠ savedClock›.symm).trans (hcontrol savedClock (by simp)))
  obtain ⟨output,rest,hhead,hrest,rfl⟩ := List.forall₂_cons_left_iff.mp herror
  have hnil : rest = [] := List.forall₂_nil_left_iff.mp hrest
  subst rest
  obtain ⟨Zs,houtput,happrox⟩ := hhead
  obtain ⟨G,Gs,hfield,hGs,rfl⟩ := List.forall₂_cons_left_iff.mp happrox
  have hnil : Gs = [] := List.forall₂_nil_left_iff.mp hGs
  subst Gs
  have hresult : initial.R result = [] :=
    (hf result ‹src ≠ result›.symm ‹result ≠ clock›).trans (hcontrol result (by simp))
  simp only [houtput,FamilyDispatchInput.normalizedOutput,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,hresult] at he
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil] at hcost
  have hbound : n ≤ r.gridCost p l t work+2*(descriptorScheduleTape work FamilyDispatchInput.words [r]).length+19 := by omega
  refine ⟨v',n,G,huser,hbound,he,?_⟩
  intro i
  exact hfield i (by change i ∈ haloVertices s 0 s; rw [haloVertices_full]; exact Finset.mem_univ i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
