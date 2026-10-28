module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedDispatchRecords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! The actual restored descriptor dispatcher satisfies the selected complete-key fast-time envelope. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open Filter IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem selectedFamilyDispatch_spec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (ct : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop,
    ∀ (h : Sizes.Big N) (i : Fin (Sizes.d N)), ∀ [NeZero (Sizes.s N i)],
    let p := Sizes.p N
    let s := Sizes.s N i
    let t := Sizes.t N i
    let l := haloInverseRingLog s t
    ∀ (d : ℝ) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A))
      (key : FamilyDispatchInput s A → Cost.SelectedFamilyKey N i ct)
      (hkeys : (records.map key).Nodup) (hmatch : ∀ r ∈ records, Cost.MatchesSelectedFamilyKey r (key r)) (hready : ∀ r ∈ records, FamilyDispatchReady p l t d r)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => (value (r.precision p l t) (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => (value (r.precision p l t) (F i)).im))
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work (familyInverseCoreReg i)) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work FamilyDispatchInput.words records++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []),
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧
      (n : ℝ) ≤ 64000*(Sizes.T N : ℝ)+(records.map (fun r => (r.inputs.length : ℝ)*D*(t : ℝ)*
        (1+(PhaseCellBand.width p r.u : ℝ)^2/Sizes.d N)*(p : ℝ)^(129/128 : ℝ))).sum+10 ∧
      Exec body (familyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs ∧
      ∀ C, mnProgPush (familyDispatch work src saved count tmp spare result clock savedClock
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map (fun r => r.stock p l t work)).sum+6*records.length+
            2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8))
          depth (familyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
          (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  obtain ⟨D,hD,hledger⟩ := Cost.selectedFamilyDispatchLedger_fast_le ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hledger] with N hn
  intro h i _
  dsimp only
  intro d hgap records key hkeys hmatch hready x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  obtain ⟨v',steps,outputs,hu,ht,he,ha,htrace⟩ := familyDispatch_exec_trace (body := body) work hwork
    src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA
    (by have := h.thirteen_le_p; omega) (h.good.lt i) (h.quarter_p_le_theta i) hgap
    records hready x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  have htime : (steps : ℝ) ≤ (((records.map (fun r => r.cost (Sizes.p N)
      (haloInverseRingLog (Sizes.s N i) (Sizes.t N i)) (Sizes.t N i) work+3)).sum+
      6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) := by
    exact_mod_cast ht
  exact ⟨v',steps,outputs,hu,htime.trans (hn h i T A work d records key hkeys hmatch hready),he,ha,htrace⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
