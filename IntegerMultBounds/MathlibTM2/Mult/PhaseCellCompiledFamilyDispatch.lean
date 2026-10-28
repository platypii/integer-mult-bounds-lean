module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyDispatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedDispatchStock
public import IntegerMultBounds.MathlibTM2.StackCompileInvariant
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorTapeCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorListLoop

/-! The same fast numerical dispatcher has a compiled stock bound at every machine configuration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open Filter IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {P U : Type} [Fintype P] {body : P → Pr P T Q A U}

theorem selectedFamilyDispatch_compiled_spec (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (main : P) (hmain : body main = familyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
    (ct : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∃ E : ℕ, ∀ᶠ N : ℕ in atTop,
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
      ((n+2 : ℕ) : ℝ) ≤ 64000*(Sizes.T N : ℝ)+(records.map (fun r => (r.inputs.length : ℝ)*D*(t : ℝ)*
        (1+(PhaseCellBand.width p r.u : ℝ)^2/Sizes.d N)*(p : ℝ)^(129/128 : ℝ))).sum+12 ∧
      Exec body (familyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
        (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) ∧
      List.Forall₂ (FamilyDispatchProduced p l t x y) records outputs ∧
      ReachWithin (mcode body main)
        (fun c => compiledSize body c ≤ mnSize (mk v S)+
          E*(records.map (fun r => r.inputs.length*s*r.width p l t)).sum+1+Sizes.T N)
        (cfg (some .entry) (mk v S) none []) (n+2)
        (cfg none (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) none []) := by
  let C := max (mnProgPush (familyDispatch work src saved count tmp spare result clock savedClock
    (P := P) (U := U) (A := A) recovery hR hQ)) (mnPushC body)
  obtain ⟨D,hD,hspec⟩ := selectedFamilyDispatch_spec (body := body) work hwork
    src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA ct
  refine ⟨D,hD,32000*(C+1),?_⟩
  filter_upwards [hspec,selectedFamilyDispatchStockLedger_scaled_volume_le ct (C+1)] with N hn hs
  intro h i _
  dsimp only
  intro d hgap records key hkeys hmatch hready x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  obtain ⟨v',steps,outputs,hu,ht,he,ha,htrace⟩ := hn h i d hgap records key hkeys hmatch hready
    x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  have hstock := hs h i T A work d records key hkeys hmatch hready
  have hw := htrace C (le_max_left _ _)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_right _ _)) 1
  have hc : ExecWithin body
      (fun depth z => mnSize z+depth ≤ mnSize (mk v S)+
        (32000*(C+1))*(records.map (fun r => r.inputs.length*Sizes.s N i*
          r.width (Sizes.p N) (haloInverseRingLog (Sizes.s N i) (Sizes.t N i)) (Sizes.t N i))).sum+1+Sizes.T N)
      1 (body main) (mk v S) steps
      (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
    rw [hmain]
    apply hw.mono
    intro depth z hz
    change mnSize z+depth ≤ mnSize (mk v S)+1+(C+1)*
      ((records.map (fun r => r.stock (Sizes.p N) (haloInverseRingLog (Sizes.s N i) (Sizes.t N i)) (Sizes.t N i) work)).sum+
        6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8) at hz
    omega
  refine ⟨v',steps,outputs,hu,?_,he,ha,hc.stock_run_main⟩
  push_cast
  linarith only [ht]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
