module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCompiledGridFamilyDispatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchOperator
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedDispatchB0
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGridDispatch
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! Production inverse execution with exact-operator error, unit-ball, fast-time and compiled-stock guarantees. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open Filter IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} [Fintype P] {body : P → Pr P T Q A U}

theorem selectedGridFamilyDispatch_operator_spec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (main : P) (hmain : body main = gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
    (ct : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∃ E : ℕ, ∀ᶠ N : ℕ in atTop,
    ∀ (h : Sizes.Big N) (i : Fin (Sizes.d N)), ∀ [NeZero (Sizes.s N i)],
    let p := Sizes.p N
    let s := Sizes.s N i
    let t := Sizes.t N i
    let l := haloInverseRingLog s t
    ∀ (d : ℝ) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A))
      (key : FamilyDispatchInput s A → Cost.SelectedFamilyKey N i ct)
      (hkeys : (records.map key).Nodup) (hmatch : ∀ r ∈ records, Cost.MatchesSelectedFamilyKey r (key r)) (hready : ∀ r ∈ records, GridDispatchReady p l t d r)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (hfull : ∀ r ∈ records, r.a = 0 ∧ r.b = s) (htarget : ∀ r ∈ records, p+8 ≤ r.target)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : ∀ r ∈ records, J r ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work FamilyDispatchInput.words records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []),
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧
      ((n+2 : ℕ) : ℝ) ≤ 2624000*(Sizes.T N : ℝ)+(records.map (fun r => (r.inputs.length : ℝ)*D*(t : ℝ)*
        (1+(PhaseCellBand.width p r.u : ℝ)^2/Sizes.d N)*(p : ℝ)^(129/128 : ℝ))).sum+412 ∧
      Exec body (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ (NormalizedDispatchProduced p x y) records outputs ∧
      List.Forall₂ (NormalizedOperatorProduced p J) records outputs ∧
      ReachWithin (mcode body main)
        (fun c => compiledSize body c ≤ mnSize (mk v S)+
          E*(records.map (fun r => r.inputs.length*s*r.width p l t)).sum+1+Sizes.T N)
        (cfg (some .entry) (mk v S) none []) (n+2)
        (cfg none (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) none []) := by
  obtain ⟨D,hD,E,hspec⟩ := selectedGridFamilyDispatch_compiled_spec (body := body) work hwork
    src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA main hmain ct
  refine ⟨D,hD,E,?_⟩
  filter_upwards [hspec] with N hn
  intro h i _
  dsimp only
  intro d hgap records key hkeys hmatch hready x y hx hy hfull htarget J hJ
    v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  letI : NeZero (Sizes.t N i) := ⟨by have hs := NeZero.ne (Sizes.s N i); have ht := h.good.lt i; omega⟩
  obtain ⟨v',steps,outputs,hu,ht,he,ha,hstock⟩ := hn h i d hgap records key hkeys hmatch hready
    x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  have hoperator := normalizedDispatchProduced_full_operator (by have := h.thirteen_le_p; omega : 4 ≤ Sizes.p N)
    (h.good.lt i) (h.quarter_p_le_theta i) hgap records hready hfull htarget x y hx hy J hJ outputs ha
  exact ⟨v',steps,outputs,hu,ht,he,ha,hoperator,hstock⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
