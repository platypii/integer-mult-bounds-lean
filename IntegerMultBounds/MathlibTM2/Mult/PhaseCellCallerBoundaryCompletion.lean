module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPreparedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRestoringBoundaryPublication

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
  ScalarPlacement ScalarPlacement.FullLineInputPlan ScalarPlacement.ComputedClassBanks CommonClassGeometry PackedTranspose
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q A U}
noncomputable section

/-- Complete a proper-published bank by solving one shared full line and
publishing its three boundary crops, restoring all temporary storage. -/
def callerBoundaryCompletion (src : Fin 11 → Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (widthSource : Fin (T+solverRegisterCount)) (recovery : Bool) :
    Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  .seq (callerPreparedBoundarySolve src hR hQ widthSource recovery)
    (callerRestoringBoundaryPublication (fun i => solverSource (src i)) widthSource)

theorem callerBoundaryCompletion_exec (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (widthSource : Fin (T+solverRegisterCount))
    (D coreWidth : ℕ) (hw : 0 < coreWidth) (hroom : 3*coreWidth < s) (recovery : Bool) (hA : 96 ≤ A)
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
    (hheaders : ∀ i : Fin 6, S.R (fullHeader _ (.publication (Fin.castAdd 1 i))) = [])
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = [])
    (hW : 2*p+13 ≤ W) (hvolumeFit : s*W < 2^D)
    (hD : (S.R (unarySource _ widthSource)).length = D)
    (hscalars : ∀ i, S.R (globals _ i) = binSyms D
      (globalValues p u l target s t (inverseCallerWordWidth p u l target s t) W Fs.length radius coreWidth i))
    (band n : ℕ) (proper : CorePublicationClass s coreWidth)
    (hr : 0 < n*band) (hrw : n*band ≤ coreWidth)
    (hproper : proper.indices = coreGatherIndices s coreWidth (n*band) (coreWidth+2*(n*band)))
    (outputTail : List (Fin (A+4))) (ambient : List (List (Fin (A+4))))
    (hgood : proper.BankAccurate p W (inversePublicationTargets p Fs J) ambient (3/(2:ℝ)^p))
    (hdst : S.R (fullHeader _ .output) = ambient.flatten++outputTail)
    (C : ℕ) (hpush : mnProgPush ((callerFullLineProducer T Q hR hQ).gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let B := inverseCallerWordWidth p u l target s t
    let F := callerPreparedBoundaryState widthSource p s coreWidth S
    let producer := callerFullLineProducer T Q hR hQ
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    let generateTime := ((2*p+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D s coreWidth (2*p+13)+(2*D+2)
    let generateStock := 2*(4*D+4)+3*boundaryCountExportCost D s coreWidth (2*p+13)
    let prepareTime := (4*p+5)+(generateTime+((4*B+5)+((solveTime+(242*volume+45))+(2*B+3))))
    let prepareStock := 13*(4*p+5)+(generateStock+(2*(4*B+5)+(solveStock+(480*volume+86))))
    let pairs := boundarySeamMasterCopies (boundaryArchiveSource (T+solverRegisterCount))
      (boundaryArchiveDestination (T+solverRegisterCount))
      (seamMasterSources (T+solverRegisterCount) (fun i => solverSource (src i)) widthSource)
    let loadCost := (pairs.map (fun pair => 6*(F.R pair.1).length+6)).sum+1
    let retireCost := 2*(pairs.map (fun pair => (F.R pair.1).length)).sum+2*pairs.length+1
    let clearCost := 2*((callerPreparedTemporaryHeaders (T+solverRegisterCount)).map (fun i => (F.R i).length)).sum+
      2*(callerPreparedTemporaryHeaders (T+solverRegisterCount)).length+1
    let publicationTime := (loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost)+clearCost
    let publicationStock := 2*loadCost+13*boundarySeamBudget r.inputs.length D s W
    ∃ output : List (List (Fin (A+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i‖ ≤ 1) ∧
        (∀ i : ZMod s, ‖pairedCellRead p W line i-target i‖ ≤ 3/(2:ℝ)^p))
        (seamPublicationTargets p r (fun _ => J)) output ∧
      ∃ v' m, v'.user = v.user ∧ m ≤ prepareTime+publicationTime ∧
        mnSize (mk v' {S with R := Function.update S.R (fullHeader _ .output) (output.flatten++outputTail)}) =
          mnSize (mk v S) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(prepareStock+publicationStock)) depth
          (callerBoundaryCompletion src hR hQ widthSource recovery) (mk v S) m
          (mk v' {S with R := Function.update S.R (fullHeader _ .output) (output.flatten++outputTail)}) := by
  dsimp only [CorePublicationClass.BankAccurate] at hgood
  dsimp only
  let r := fullLineGridRecord (A := A) p u l target t Fs
  let seedValue := fun i : Fin 117 => if i = 55 then s else if i = 56 then coreWidth else W
  have hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,coreWidth,W] j := by
    intro j; fin_cases j <;> simp [seedValue,boundarySeedGlobals]
  have hsW : s ≤ s*W := Nat.le_mul_of_pos_right _ (by omega)
  have hWW : W ≤ s*W := Nat.le_mul_of_pos_left _ (by omega)
  have hfit : ∀ j, seedValue (boundarySeedGlobals j) < 2^D := by
    intro j
    rw [hvalues j]
    fin_cases j
    · change s < 2^D; omega
    · change coreWidth < 2^D; omega
    · change W < 2^D; omega
  obtain ⟨v₁,n₁,solverOutput,banks,hu₁,hn₁,hproduced,hbanks,he₁⟩ := callerPreparedBoundarySolve_exec
    src hsrc hR hQ widthSource D coreWidth hw hroom recovery hA hp hst hu hwidth hθ hgap hbudget hband hpad htarget
    Fs hFs X Y hX hY J hJ W radius v S hraw hzero hblank hleft hambient (hheaders 3) hprivate
    (lt_of_le_of_lt (Nat.mul_le_mul_left s hW) hvolumeFit) hD
    (by simpa [globalValues] using hscalars 4)
    (by simpa [globalValues] using hscalars 10)
    (by intro j; exact hheaders ⟨4+j.val,by have := j.isLt; omega⟩)
    (fun slot => hheaders (Fin.castAdd 3 slot)) C hpush hbody depth
  obtain ⟨output,haccuracy,v₂,n₂,hu₂,hn₂,he₂⟩ := callerRestoringBoundaryPublication_exec body
    (fun i => solverSource (src i)) widthSource p u l target t (inverseCallerWordWidth p u l target s t)
    W D radius coreWidth band n (by omega) hW hw hroom hvolumeFit seedValue hvalues hfit
    r (fun _ => J) proper hr hrw hproper outputTail S hraw hD hscalars hzero hheaders hprivate
    banks hbanks ambient hgood hdst depth v₁
  have hrowCount : output.length = ambient.length := haccuracy.length_eq.symm.trans hgood.length_eq
  have houtputLength : ∀ line ∈ output, line.length = s*W :=
    (List.forall₂_and_left _ _).mp haccuracy.flip |>.1
  have hambientLength : ∀ line ∈ ambient, line.length = s*W :=
    (List.forall₂_and_left _ _).mp hgood.flip |>.1
  have hlength : (output.flatten++outputTail).length = (S.R (fullHeader _ .output)).length := by
    rw [hdst]
    simp only [List.length_append,length_flatten_const _ houtputLength,
      length_flatten_const _ hambientLength,hrowCount]
  have hstock := mn_replace_right_size_of_length v v₂ S (fullHeader _ .output) (output.flatten++outputTail) hlength
  refine ⟨output,haccuracy,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hstock,?_⟩
  have hpoint := he₁.final
  apply ExecWithin.seq
  · exact he₁.mono (by intro d z hz; omega)
  · exact he₂.mono (by intro d z hz; dsimp only [r,callerPreparedBoundaryState] at hpoint hz ⊢; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
