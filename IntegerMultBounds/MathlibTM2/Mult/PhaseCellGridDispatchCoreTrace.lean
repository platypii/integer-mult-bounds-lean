module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGridDispatchTrace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedDispatchCoreAccuracy

/-! The restored production dispatch supplies global accuracy on generated cores,
for the same bytes, time bound and execution-wide stock certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def GeneratedCoreProduced (p width target : ℕ) (k : FamilyDispatchInput s A → ℕ)
    (X Y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (r : FamilyDispatchInput s A) (output : List (Fin (A+4))) : Prop :=
  ∃ Zs, output = r.normalizedOutput p Zs ∧
    List.Forall₂ (fun F Z => ErrorOn (ownedCore s width (k r))
      (pairedCellRead p (2*p+13) (cstream A (2*p+13) (chirpLine s Z)))
      (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(⟨X r F i,Y r F i⟩ : ℂ))
      ((2/(2 : ℝ)^p+(1/(2 : ℝ)^r.target)/(2 : ℝ)^inverseNormalizationShift p)+
        (1/(2 : ℝ)^target+1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)) r.inputs Zs

theorem gridFamilyDispatch_generated_core_exec_trace (work : Fin 303 → Fin T) (hwork : Function.Injective work)
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
    (width target : ℕ) (k : FamilyDispatchInput s A → ℕ)
    (hhalo : ∀ r ∈ records, haloVertices s r.a r.b = (PhaseCellInterface.generatedWindow s width p r.u target (k r)).halo)
    (X Y : FamilyDispatchInput s A → (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ
      (X r F) (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ r ∈ records, ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ
      (Y r F) (fun i => ((1/2 : ℂ)*value p (F i)).im))
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
      List.Forall₂ (GeneratedCoreProduced p width target k X Y) records outputs ∧
      ∀ C, mnProgPush (gridFamilyDispatch work src saved count tmp spare result clock savedClock
        (P := P) (U := U) (A := A) recovery hR hQ) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*((records.map (fun r => r.gridStock p l t work)).sum+6*records.length+
            2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8))
          depth (gridFamilyDispatch work src saved count tmp spare result clock savedClock recovery hR hQ)
          (mk v S) n (mk v' {S with R := Function.update S.R result (outputs.reverse.flatten++S.R result)}) := by
  obtain ⟨v',n,outputs,hu,hn,he,ha,hstock⟩ := gridFamilyDispatch_exec_trace (body := body)
    work hwork src saved count tmp spare result clock savedClock hreg hsep recovery hR hQ hA
    hp hst hθ hgap records hready x y hx hy v S rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  refine ⟨v',n,outputs,hu,hn,he,?_,hstock⟩
  have hm := (List.forall₂_and_left records outputs).mpr ⟨fun _ hr => hr,ha⟩
  apply List.Forall₂.imp _ hm
  intro r output hpair
  obtain ⟨hr,Zs,hout,happrox⟩ := hpair
  have hα : 0 < Real.sqrt (r.u : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (hready r hr).uPositive)
  have hαu : (Real.sqrt (r.u : ℝ))^2 = (r.u : ℝ) := Real.sq_sqrt (by positivity)
  refine ⟨Zs,hout,NormalizedDispatchApprox.generated_core_accuracy r width target (k r)
    hst hα hp (hready r hr).width hαu hθ hgap (by rw [hαu]; exact (hready r hr).budget)
    (hhalo r hr) (x r) (y r) (X r) (Y r) _ _ (hx r hr) (hy r hr) (hX r hr) (hY r hr) ?_ ?_ Zs happrox⟩
  · intro F hF i
    have hnorm : ‖(1/2 : ℂ)*value p (F i)‖ ≤ (1/2 : ℝ) := by
      rw [norm_mul]
      have hunit := (hready r hr).inputBound F hF i
      norm_num
      linarith
    exact (Complex.abs_re_le_norm _).trans hnorm
  · intro F hF i
    have hnorm : ‖(1/2 : ℂ)*value p (F i)‖ ≤ (1/2 : ℝ) := by
      rw [norm_mul]
      have hunit := (hready r hr).inputBound F hF i
      norm_num
      linarith
    exact (Complex.abs_im_le_norm _).trans hnorm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
