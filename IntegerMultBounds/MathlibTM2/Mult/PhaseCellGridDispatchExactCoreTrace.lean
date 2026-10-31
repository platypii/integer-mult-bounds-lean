module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCoreExactInverse

/-! Actual dispatch carries exact-inverse core accuracy for its returned bytes,
with the original restoration, time and execution-wide stock guarantees. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def ExactCoreProduced (p width : ℕ) (k : FamilyDispatchInput s A → ℕ)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (r : FamilyDispatchInput s A) (output : List (Fin (A+4))) : Prop :=
  ∃ Zs, output = r.normalizedOutput p Zs ∧
    List.Forall₂ (fun F Z =>
      let out := pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z))
      (∀ i ∈ ownedCore s width (k r), ‖out i‖ ≤ 1) ∧
      ErrorOn (ownedCore s width (k r)) out
        ((((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J r) ((1/2 : ℂ) • fun i => value p (F i)))
        (3/(2 : ℝ)^p)) r.inputs Zs

theorem gridFamilyDispatch_exact_core_exec_trace (work : Fin 303 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l t : ℕ} [NeZero t] {d : ℝ} (hp : 4 ≤ p) (hst : s < t)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (records : List (FamilyDispatchInput s A)) (hready : ∀ r ∈ records, GridDispatchReady p l t d r)
    (x y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (x r F) (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hy : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b)
      (y r F) (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (width target : ℕ) (k : FamilyDispatchInput s A → ℕ)
    (hhalo : ∀ r ∈ records, haloVertices s r.a r.b = (PhaseCellInterface.generatedWindow s width p r.u target (k r)).halo)
    (X Y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ
      (X r F) (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ
      (Y r F) (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (htarget : p+2 ≤ target) (hprecision : ∀ r ∈ records, r.target = target)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : ∀ r ∈ records, J r ∘L PhaseCellOperator.exact s t (Real.sqrt (r.u : ℝ)) = 1)
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
      List.Forall₂ (ExactCoreProduced p width k J) records outputs ∧
      ∀ C, mnProgPush (gridFamilyDispatch work src saved count tmp spare result clock savedClock
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map (fun r => r.gridStock p l t work)).sum+6*records.length+
            2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8))
          depth (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
          (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  obtain ⟨v',n,outputs,hu,hn,he,ha,hstock⟩ := gridFamilyDispatch_generated_core_exec_trace (body := body)
    work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA
    (by omega) hst hθ hgap records hready x y hx hy width target k hhalo X Y hX hY
    v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  refine ⟨v',n,outputs,hu,hn,he,?_,hstock⟩
  have hm := (List.forall₂_and_left records outputs).mpr ⟨fun _ hr => hr,ha⟩
  apply List.Forall₂.imp _ hm
  intro r output hpair
  obtain ⟨hr,hproduced⟩ := hpair
  have hcore : GeneratedCoreProduced p width r.target k X Y r output := by
    rw [hprecision r hr]
    exact hproduced
  exact hcore.exact_inverse hp hst hθ hgap r (hready r hr)
    (by rw [hprecision r hr]; exact htarget) k X Y (hX r hr) (hY r hr) (J r) (hJ r hr) output

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
