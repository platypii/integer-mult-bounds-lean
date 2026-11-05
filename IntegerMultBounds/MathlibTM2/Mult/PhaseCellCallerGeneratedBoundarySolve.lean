module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerInitializedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerGenerateBoundaryGeometry

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

/-- Generate boundary controls from retained dimensions, then solve and crop
once with the concrete restoring solver lifecycle. -/
def callerGeneratedBoundarySolve (src : Fin 11 → Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (widthSource : Fin (T+solverRegisterCount)) (recovery : Bool) :
    Pr P (MachineTapes (T+solverRegisterCount)) Q A U :=
  .seq (callerBoundaryGeometryProgram widthSource) (callerInitializedBoundarySolve src hR hQ recovery)

theorem callerGeneratedBoundarySolve_exec (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4)
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
    (hword : (S.R (fullHeader _ (.publication 3))).length = 2*p+13)
    (hprivate : ∀ i : Fin tapeCount, S.R (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) i) = [])
    (hvolumeFit : s*(2*p+13) < 2^D)
    (hD : (S.R (unarySource _ widthSource)).length = D)
    (hlineBinary : S.R (globals _ 4) = binSyms D s)
    (hwidthBinary : S.R (globals _ 10) = binSyms D coreWidth)
    (hskip : ∀ j : Fin 2, S.R (fullHeader _ (.publication ⟨4+j.val,by omega⟩)) = [])
    (hcounts : ∀ slot : Fin 3, S.R (fullHeader _ (.publication (Fin.castAdd 4 slot))) = [])
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
    let generateTime := ((2*p+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D s coreWidth (2*p+13)+(2*D+2)
    let generateStock := 2*(4*D+4)+3*boundaryCountExportCost D s coreWidth (2*p+13)
    ∃ v' n output, ∃ banks : List (List (List GaussianInt)),
      v'.user = v.user ∧ n ≤ generateTime+((4*B+5)+((solveTime+(242*volume+45))+(2*B+3))) ∧
      ExactCoreProduced p s (fun _ => 0) (fun _ => J) r output ∧
      List.Forall₂ (SeamCropRows p coreWidth r (fun _ => J)) (boundaryCropSchedule s coreWidth).reverse banks ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (generateStock+(2*(4*B+5)+(solveStock+(480*volume+86))))) depth
        (callerGeneratedBoundarySolve src hR hQ widthSource recovery) (mk v S) n
        (mk v' {F with R := (Function.update F.R (fullHeader (T+solverRegisterCount) (.publication 6))
          ((banks.map (fun rows => cstream A (2*p+13) rows.flatten)).flatten++S.R (fullHeader (T+solverRegisterCount) (.publication 6))))}) := by
  dsimp only
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := callerBoundaryGeometry_exec body widthSource D s coreWidth (2*p+13)
    hw (by omega) hroom hvolumeFit v S hD hlineBinary hwidthBinary hword hzero hskip hcounts hprivate depth
  obtain ⟨v₂,n₂,output,banks,hu₂,hn₂,hproduced,hbanks,he₂⟩ := callerInitializedBoundarySolve_exec
    src hsrc hR hQ widthSource coreWidth hw hroom recovery hA hp hst hu hwidth hθ hgap hbudget hband hpad htarget
    Fs hFs X Y hX hY J hJ W radius v₁ S hraw hzero hblank hleft hambient hword hprivate C hpush hbody depth
  refine ⟨v₂,n₁+n₂,output,banks,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,hproduced,hbanks,?_⟩
  have hpoint := he₁.final
  apply ExecWithin.seq
  · exact he₁.mono (by intro d z hz; omega)
  · exact he₂.mono (by intro d z hz; omega)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
