module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolverGeometryWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSolveBoundaryCrops

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
  ScalarPlacement ScalarPlacement.FullLineInputPlan CommonClassGeometry PackedTranspose
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U}
noncomputable section

def callerSolverCropSources (src : Fin 11 → Fin T) : Fin 2 → Fin (T+solverRegisterCount) :=
  ![solverSource (src 8),solverSource (src 4)]

theorem callerSolverCropSources_injective (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4) :
    Function.Injective (callerSolverCropSources src) := by
  have hn : callerSolverCropSources src 0 ≠ callerSolverCropSources src 1 :=
    (Fin.castAdd_injective _ _).ne hsrc
  intro i j he
  fin_cases i <;> fin_cases j
  · rfl
  · exact (hn he).elim
  · exact (hn he.symm).elim
  · rfl

theorem callerSeededBoundarySolve_exec (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (widthSource : Fin (T+solverRegisterCount))
    (coreWidth : ℕ) (hw : 0 < coreWidth) (hroom : 3*coreWidth < s) (recovery : Bool) (hA : 96 ≤ A)
    {p u l target t : ℕ} [NeZero t] {d : ℝ}
    (hp : 4 ≤ p) (hst : s < t) (hu : 1 ≤ u) (hwidth : 8*p ≤ 2^u)
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (hbudget : (u : ℝ)*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (htarget : p+2 ≤ target)
    (Fs : List (ZMod s → GaussianInt)) (hFs : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F)
      (fun i => ((1/2 : ℂ)*value p (F i)).re))
    (hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => ((1/2 : ℂ)*value p (F i)).im))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (W radius : ℕ) (v : HS (MachineTapes (T+solverRegisterCount)) Q A U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) A)
    (hraw : ∀ i, (S.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t (inverseCallerWordWidth p u l target s t) W Fs.length radius coreWidth i)
    (hzero : S.R (fullHeader _ .zero) = [])
    (hblank : ∀ r : SolverRole, r ≠ .scratch 4 → S.R (solverRegister T r) = [])
    (hleft : ∀ r : SolverRole, S.L (solverRegister T r) = [])
    (hambient : S.R (solverRegister T (.scratch 4)) =
      cstream A (inverseFullInputWidth p u l target s t) (Fs.map (chirpLine s)).flatten)
    (hword : (S.R (fullHeader _ (.publication 3))).length = 2*p+13)
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = [])
    (C : ℕ) (hpush : mnProgPush ((callerFullLineProducer T Q hR hQ).gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) (callerSolverWidthState B S)
    let producer := callerFullLineProducer T Q hR hQ
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    ∃ v' n output, ∃ banks : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ solveTime+(242*volume+45) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) (boundaryCropSchedule s coreWidth).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        (solveStock+(480*volume+86))) depth
        (callerSolveBoundaryCrops (callerFullLineInput T src) producer (callerSolverCropSources src) recovery) (mk v F) n
        (mk v' {F with R := (Function.update F.R (fullHeader (T+solverRegisterCount) (.publication 6))
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader (T+solverRegisterCount) (.publication 6))))}) := by
  dsimp only
  let B := inverseCallerWordWidth p u l target s t
  let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) S
  let M := callerSolverWidthState B S
  let input := callerFullLineInput T src
  let producer := callerFullLineProducer T Q hR hQ
  let cropSources := callerSolverCropSources src
  let port : Fin tapeCount → Fin (MachineTapes (T+solverRegisterCount)) := Fin.natAdd (((T+solverRegisterCount)+headerCount)+175)
  have hread (k : Fin (MachineTapes (T+solverRegisterCount)))
      (hk : k ≠ solverRegister T (.input (familyInverseScalarReg .wr))) : M.R k = S.R k := by
    dsimp only [M,callerSolverWidthState]
    exact Function.update_of_ne hk _ _
  have hrole (r : SolverRole) (hr : r ≠ .input (familyInverseScalarReg .wr))
      (hc : r ≠ .scratch 4) : M.R (solverRegister T r) = [] :=
    (hread _ ((solverRegister_injective T).ne hr)).trans (hblank r hc)
  have hrawM (i : Fin 11) : (M.R (unarySource _ (solverSource (src i)))).length =
      globalValues p u l target s t B W Fs.length radius coreWidth i := by
    rw [hread _ (solverRegister_ne_source T (.input (familyInverseScalarReg .wr)) (src i)).symm]
    exact hraw i
  have hzeroM : M.R (fullHeader _ .zero) = [] :=
    (hread _ (solverRegister_ne_header T (.input (familyInverseScalarReg .wr)) .zero).symm).trans hzero
  have hprivateM (i : Fin tapeCount) : M.R (port i) = [] :=
    (hread _ (solverRegister_ne_routing T (.input (familyInverseScalarReg .wr)) i).symm).trans (hprivate i)
  have hreadyM := callerSolverWidthState_ready src p u l target t W radius coreWidth Fs S
    hraw hzero hblank (fun i => hleft (.input i)) hambient
  obtain ⟨v₂,n₂,output,banks,hu₂,hn₂,hproduced,hbanks,he₂⟩ := callerSolveBoundaryCrops_exec
    input producer (callerFullLine_compatible T Q src hR hQ) cropSources
    (callerSolverCropSources_injective src hsrc) widthSource coreWidth hw hroom
    (callerFullLine_result T cropSources) recovery hA hp hst hu hwidth hθ hgap hbudget hband hpad htarget
    Fs hFs X Y hX hY J hJ v M hreadyM hzeroM
    (callerFullLine_controls_separated T Q src hR hQ widthSource)
    (fun i => hrole (.worker (Fin.castLE (by decide : 303 ≤ 325) i)) (by simp) (by simp))
    (fun i => hleft (.worker (Fin.castLE (by decide : 303 ≤ 325) (familyInverseCoreReg i))))
    (by
      intro k hk
      change k ∈ [solverRegister T (.control 2),solverRegister T (.control 3),solverRegister T (.control 4),
        solverRegister T (.control 5),solverRegister T (.control 1),solverRegister T (.control 6)] at hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hrole _ (by simp) (by simp))
    (by simpa [cropSources,callerSolverCropSources,globalValues] using hrawM 8)
    (by simpa [cropSources,callerSolverCropSources,globalValues] using hrawM 4)
    (by rw [hread _ (solverRegister_ne_header T (.input (familyInverseScalarReg .wr)) (.publication 3)).symm]; exact hword)
    hprivateM C hpush hbody depth
  have harc : boundaryCropRegister (T+solverRegisterCount) cropSources 95 = fullHeader (T+solverRegisterCount) (.publication 6) :=
    boundaryCropRegister_archive (T+solverRegisterCount) cropSources
  have hreadArc : M.R (fullHeader (T+solverRegisterCount) (.publication 6)) = S.R (fullHeader (T+solverRegisterCount) (.publication 6)) :=
    hread _ (solverRegister_ne_header T (.input (familyInverseScalarReg .wr)) (.publication 6)).symm
  rw [harc,hreadArc] at he₂
  exact ⟨v₂,n₂,output,banks,hu₂,hn₂,hproduced,hbanks,he₂⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
