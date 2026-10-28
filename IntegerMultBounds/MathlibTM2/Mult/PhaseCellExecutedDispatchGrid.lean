module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSingletonGridDispatch
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! A singleton descriptor executes the actual restored production dispatcher. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance

variable {T Q A s : ℕ} [NeZero s] {U : Type}

def DispatchGridResult (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (p u l target t : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (F G : ZMod s → GaussianInt) : Prop :=
  let initial := singletonGridDispatchState work src clock p u l target t F S
  ∃ v' n, Exec (fun f : Empty => nomatch f)
    (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
    (mk v initial) n (mk v' {initial with R := Function.update initial.R result (cstream A (2*p+13) (chirpLine s G))})

noncomputable def executedDispatchGridOutput (work : Fin 303 → Fin T)
    (src saved count tmp spare result clock savedClock : Fin T) (recovery : Bool)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (p u l target t : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (F : ZMod s → GaussianInt) : ZMod s → GaussianInt := by
  classical
  exact if h : ∃ G, DispatchGridResult work src saved count tmp spare result clock savedClock
    recovery hR hQ p u l target t v S F G then Classical.choose h else 0

theorem executedDispatchGrid_spec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target t : ℕ} {α d : ℝ}
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
    ∃ v' n, v'.user = v.user ∧
      n ≤ r.gridCost p l t work+2*(descriptorScheduleTape work FamilyDispatchInput.words [r]).length+19 ∧
      Exec (fun f : Empty => nomatch f) (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v initial) n (mk v' {initial with R := Function.update initial.R result (cstream A (2*p+13) (chirpLine s (executedDispatchGridOutput work src saved count tmp spare result clock savedClock recovery hR hQ p u l target t v S F)))}) ∧
      ∀ i, ‖pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s (executedDispatchGridOutput work src saved count tmp spare result clock savedClock recovery hR hQ p u l target t v S F))) i-
        ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨yr i,yi i⟩ : ℂ)‖ ≤
          2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p := by
  obtain ⟨vi,n,G,hui,hn,hei,herror⟩ := singletonGridDispatch_exec (body := fun f : Empty => nomatch f)
    work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA
    hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad F hF v S hblank hleft hcontrol yr yi hyr hyi
  have hex : ∃ G, DispatchGridResult work src saved count tmp spare result clock savedClock
      recovery hR hQ p u l target t v S F G := ⟨G,vi,n,hei⟩
  have hchosen : DispatchGridResult work src saved count tmp spare result clock savedClock
      recovery hR hQ p u l target t v S F
      (executedDispatchGridOutput work src saved count tmp spare result clock savedClock recovery hR hQ p u l target t v S F) := by
    classical
    simpa only [executedDispatchGridOutput,dite_eq_left hex] using Classical.choose_spec hex
  obtain ⟨v',m,he⟩ := hchosen
  have hsame := he.unique hei
  have huser : v'.user = vi.user := congrArg (fun z => z.var.user) hsame.2
  have hout := congrArg (fun z => z.stk (.rt result)) hsame.2
  simp only [mk_stk,get_rt,Function.update_self] at hout
  refine ⟨v',m,huser.trans hui,by rw [hsame.1]; exact hn,he,?_⟩
  rw [hout]
  exact herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
