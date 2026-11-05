module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeededBoundarySolve

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

def callerInitializedBoundarySolve (src : Fin 11 → Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (recovery : Bool) : Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  .seq (callerSolverWidthProgram src)
    (.seq (callerSolveBoundaryCrops (callerFullLineInput T src) (callerFullLineProducer T Q hR hQ)
      (callerSolverCropSources src) recovery)
      (clearWords [solverRegister T (.input (familyInverseScalarReg .wr))]))

theorem callerInitializedBoundarySolve_exec (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4)
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
    let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) S
    let producer := callerFullLineProducer T Q hR hQ
    let r := fullLineGridRecord (A := A) p u l target t Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime p u l target s t Fs.length+
      ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock p u l target s t Fs.length+(31*tape.length+9+(C+1)*producer.gridStock p l t r)
    let volume := r.inputs.length*s*(2*p+13)
    ∃ v' n output, ∃ banks : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ (4*B+5)+((solveTime+(242*volume+45))+(2*B+3)) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) (boundaryCropSchedule s coreWidth).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        (2*(4*B+5)+(solveStock+(480*volume+86)))) depth
        (callerInitializedBoundarySolve src hR hQ recovery) (mk v F) n
        (mk v' {F with R := (Function.update F.R (fullHeader (T+solverRegisterCount) (.publication 6))
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader (T+solverRegisterCount) (.publication 6))))}) := by
  dsimp only
  let B := inverseCallerWordWidth p u l target s t
  let F := callerBoundaryGeometryState widthSource s coreWidth (2*p+13) S
  let port : Fin tapeCount → Fin (MachineTapes (T+solverRegisterCount)) := Fin.natAdd (((T+solverRegisterCount)+headerCount)+175)
  have hB : (F.R (unarySource _ (solverSource (src 6)))).length = B := by
    rw [callerSolverGeometry_off_source]
    simpa [globalValues,B] using hraw 6
  have hblankF (r : SolverRole) (hr : r ≠ .scratch 4) : F.R (solverRegister T r) = [] :=
    (callerSolverGeometry_off_register widthSource s coreWidth (2*p+13) S r).trans (hblank r hr)
  obtain ⟨v₁,hu₁,he₁⟩ := callerSolverWidth_exec body src B v F hB
    (hblankF (.input (familyInverseScalarReg .wr)) (by intro he; cases he)) (hblankF (.scratch 0) (by decide)) depth
  obtain ⟨v₂,n₂,output,banks,hu₂,hn₂,hproduced,hbanks,he₂⟩ := callerSeededBoundarySolve_exec
    src hsrc hR hQ widthSource coreWidth hw hroom recovery hA hp hst hu hwidth hθ hgap hbudget hband hpad htarget
    Fs hFs X Y hX hY J hJ W radius v₁ S hraw hzero hblank hleft hambient hword hprivate C hpush hbody depth
  rw [callerSolverGeometry_width] at he₂
  let ys := (banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader (T+solverRegisterCount) (.publication 6))
  obtain ⟨v₃,hu₃,he₃⟩ := callerSolverWidthRetire_exec body B F
    (hblankF (.input (familyInverseScalarReg .wr)) (by intro he; cases he)) (port (publicationReg 94)) (fullHeader _ (.publication 6))
    (solverRegister_ne_routing T (.input (familyInverseScalarReg .wr)) (publicationReg 94)).symm
    (solverRegister_ne_header T (.input (familyInverseScalarReg .wr)) (.publication 6)).symm
    (F.R (port (publicationReg 94))) ys v₂ depth
  have hs : (callerSolverWidthState B F).R (port (publicationReg 94)) = F.R (port (publicationReg 94)) := by
    dsimp only [callerSolverWidthState]
    exact Function.update_of_ne (solverRegister_ne_routing T (.input (familyInverseScalarReg .wr)) (publicationReg 94)).symm _ _
  have huS : Function.update (callerSolverWidthState B F).R (port (publicationReg 94))
      (F.R (port (publicationReg 94))) = (callerSolverWidthState B F).R := by
    rw [← hs,Function.update_eq_self]
  rw [huS,Function.update_eq_self] at he₃
  dsimp only [F,B,port,ys] at he₁ he₂ he₃
  refine ⟨v₃,(4*B+5)+(n₂+(2*B+3)),output,banks,hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,hproduced,hbanks,?_⟩
  have h₁ := he₁.final
  have h₂ := he₂.final
  apply ExecWithin.seq
  · exact he₁.mono (by intro d z hz; omega)
  · apply ExecWithin.seq
    · exact he₂.mono (by intro d z hz; omega)
    · exact he₃.mono (by intro d z hz; omega)


end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
