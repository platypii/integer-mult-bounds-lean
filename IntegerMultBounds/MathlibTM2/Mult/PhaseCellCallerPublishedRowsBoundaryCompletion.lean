module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerBoundaryCompletion
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCallerReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPublishedSeamBank

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

theorem callerBoundaryCompletion_of_publishedRows_exec (src : Fin 11 → Fin T) (hsrc : src 8 ≠ src 4)
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
    (ready : BoundaryCallerReady src widthSource p u l target t W D radius coreWidth Fs S)
    (hW : 2*p+13 ≤ W) (hvolumeFit : s*W < 2^D)
    (band n : ℕ) (proper : CorePublicationClass s coreWidth)
    (hr : 0 < n*band) (hrw : n*band ≤ coreWidth)
    (hproper : proper.indices = coreGatherIndices s coreWidth (n*band) (coreWidth+2*(n*band)))
    (N L : ℕ) (batch : PackedExactBatch A s t N L) (rows : batch.Rows)
    (hbatchWidth : batch.W = W) (hkeys : batch.records.map (fun job => job.k) = proper.indices)
    (F : Fin N → ZMod s → GaussianInt) (hinputs : List.ofFn F = Fs.reverse)
    (hpJobs : ∀ job ∈ batch.records, job.p = p)
    (hwidthJobs : ∀ job ∈ batch.records, job.coreWidth = coreWidth)
    (hFsJobs : ∀ job ∈ batch.records, job.Fs = Fs.reverse)
    (hJJobs : ∀ job ∈ batch.records, batch.J job = J)
    (ambient : Fin N → List (Fin (A+4))) (hlen : ∀ j, (ambient j).length = s*W)
    (outputTail : List (Fin (A+4)))
    (C : ℕ) (hpush : mnProgPush ((callerFullLineProducer T Q hR hQ).gridProgram (P := P) (U := U) (A := A) recovery) ≤ C)
    (hbody : ∀ f, mnProgPush (body f) ≤ C) (depth : ℕ) :
    let properLines := List.ofFn (fun j => proper.output W hw (rows.classRows proper hkeys j) (ambient j))
    let M : Stacks (MachineTapes (T+solverRegisterCount)) A :=
      {S with R := Function.update S.R (fullHeader _ .output) (properLines.flatten++outputTail)}
    let B := inverseCallerWordWidth p u l target s t
    let F := callerPreparedBoundaryState widthSource p s coreWidth M
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
          mnSize (mk v M) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v M)+depth+(prepareStock+publicationStock)) depth
          (callerBoundaryCompletion src hR hQ widthSource recovery) (mk v M) m
          (mk v' {S with R := Function.update S.R (fullHeader _ .output) (output.flatten++outputTail)}) := by
  dsimp only
  let r := fullLineGridRecord (A := A) p u l target t Fs
  let properLines := List.ofFn (fun j => proper.output W hw (rows.classRows proper hkeys j) (ambient j))
  let M : Stacks (MachineTapes (T+solverRegisterCount)) A :=
    {S with R := Function.update S.R (fullHeader _ .output) (properLines.flatten++outputTail)}
  have hlenBatch : ∀ j, (ambient j).length = s*batch.W := by
    intro j; rw [hbatchWidth]; exact hlen j
  have hgood := rows.published_seam_bank_good proper hkeys hw p F r hinputs (fun _ => J)
    hpJobs hwidthJobs hFsJobs hJJobs ambient hlenBatch
  rw [hbatchWidth] at hgood
  have readyM := ready.update_output (properLines.flatten++outputTail)
  obtain ⟨output,haccuracy,v',m,hu,hm,hstock,he⟩ := callerBoundaryCompletion_exec src hsrc hR hQ widthSource D coreWidth
    hw hroom recovery hA hp hst hu hwidth hθ hgap hbudget hband hpad htarget Fs hFs X Y hX hY J hJ W radius v M
    readyM.raw readyM.zero readyM.blank readyM.left readyM.input readyM.headers readyM.privateBank
    hW hvolumeFit readyM.arithmeticWidth readyM.scalars band n proper hr hrw hproper outputTail properLines hgood
    (by dsimp only [M]; exact Function.update_self _ _ _) C hpush hbody depth
  have hend : ({M with R := Function.update M.R (fullHeader _ .output) (output.flatten++outputTail)} :
      Stacks (MachineTapes (T+solverRegisterCount)) A) =
      {S with R := Function.update S.R (fullHeader _ .output) (output.flatten++outputTail)} := by
    simp only [M,Function.update_idem]
  rw [hend] at hstock he
  exact ⟨output,haccuracy,v',m,hu,hm,hstock,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
