module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInitializedPublishedClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublishedBoundaryExecution

/-! Execute the selected proper producer and actual boundary completion on the
extended caller machine. The proper execution and bank certificate are derived
from the selected theorem, rather than supplied as hypotheses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
open ComputedClassBanks CallerLayout CommonClassGeometry PackedTranspose FullLineInputPlan
open IntegerMultBounds.NLogN.SchurDominance

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem selectedPublishedBoundaryRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) :
    let physicalBank := CallerLayout.bank (solverSource ∘ bank)
    let physicalInj := bank_injective (solverSource ∘ bank) ((Fin.castAdd_injective _ _).comp hinj)
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] [NeZero (Sizes.t n₀ i)] (u target : ℕ),
    let L := amortizedCoreWidth ct (Sizes.p n₀)+
      2*(localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u)
    ∀ (_hu : u ≤ Sizes.p n₀) (_htarget : target ≤ ct*Sizes.p n₀)
    (gap : ℝ) (C : ZMod (Sizes.s n₀ i) → GaussianInt)
    (V : Fin (coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
        (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u) L)[j.val]
      PackedHaloParameterBounds (p := Sizes.p n₀)
        (l := haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (t := Sizes.t n₀ i)
        (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k (PhaseCellBand.width (Sizes.p n₀) u)
          (localityDepth (Sizes.p n₀) target)).1)
        (b := (coreHaloEndpoints (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k (PhaseCellBand.width (Sizes.p n₀) u)
          (localityDepth (Sizes.p n₀) target)).2) (V := V j) (Real.sqrt (u : ℝ)) gap C)
    (Fs : List (ZMod (Sizes.s n₀ i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n₀) (F j)‖ ≤ 1),
    let B := inverseCallerWordWidth (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
    let W := packedHaloCommonWidth (Sizes.p n₀) (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (Sizes.s n₀ i) u (target+1) 2
    let radius := localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u
    let indices := coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    ∀ (D Cprog depth Vg Vr replicaExp : ℕ),
    let rg := numericTable (T+solverRegisterCount)
    ∀
    (_hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).clock (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).work (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).count (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).spare (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).result b.hR b.hQ)) ≤ Cprog)
    (_hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (_hwide : (Sizes.s n₀ i)+(amortizedCoreWidth ct (Sizes.p n₀))+2*radius < 2^B)
    (hA : 4 ≤ (prime+K))
    (v : HS (MachineTapes (T+solverRegisterCount)) Q (prime+K) U) (base : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K))
    (borrowed : List (Fin (prime+K+4)))
    (input : SetupInput (T+solverRegisterCount) (prime+K) D (Sizes.p n₀) u
      (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
      B W Fs.length radius (amortizedCoreWidth ct (Sizes.p n₀)) Vg Vr base)
    (hgeometry : amortizedCoreWidth ct (Sizes.p n₀)+2*radius < 2^D)
    (hfit : ∀ j, globalValues (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i))
      target (Sizes.s n₀ i) (Sizes.t n₀ i) B W Fs.length radius (amortizedCoreWidth ct (Sizes.p n₀)) j < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (movement : GatherBounds Q Vg Vr (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L W replicaExp Fs)
    (hwords : ∀ f j, base.R (fullHeader (T+solverRegisterCount) (.geometry f j)) =
      binSyms (formatWidths B Vg Vr f) (![Sizes.s n₀ i,amortizedCoreWidth ct (Sizes.p n₀),radius] j))
    (retained : GatherRetainedInput (T+solverRegisterCount) K (Sizes.s n₀ i) W (solverSource ∘ bank) Fs borrowed base),
    let setup := makeSetup input false movement.widthPositive hgeometry hfit hbits
    let src := geometrySources (T+solverRegisterCount)
    let masters := masterSources (T+solverRegisterCount)
    ∀ (_caller : setup.NumericalInput (fullExposedClassBank physicalBank) rg src masters),
    let widthMaster := setup.widthMaster
    let zeroMaster := setup.zero
    let seed := makeGatherSeed input hwords (solverSource ∘ bank) retained movement
      (Nat.le_refl _) hA
    ∀ (gatherInput : setup.GatherInput seed rg masters (src 3)),
    let g := gatherInput.ready
    ∀ (_hExposeWidth : Vg ≤ cV*Sizes.p n₀) (_hRouteWidth : g.D ≤ cD*Sizes.p n₀)
    (_hMetadataFit : g.D ≤ 2^g.a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n₀ i)
      (amortizedCoreWidth ct (Sizes.p n₀)) radius L).length*(L*W))
    (_hReplicaVolume : Fs.length ≤ Sizes.T n₀)
    (hp : 4 ≤ Sizes.p n₀) (hprecision : Sizes.p n₀+2 ≤ target)
    (J : (ZMod (Sizes.s n₀ i) → ℂ) →L[ℂ] (ZMod (Sizes.s n₀ i) → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact (Sizes.s n₀ i) (Sizes.t n₀ i) (Real.sqrt (u : ℝ)) = 1),
    let batch := (PackedExactBatch.ofCommonCoreClass (A := prime+K)
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target
      (amortizedCoreWidth ct (Sizes.p n₀)) L (Real.sqrt (u : ℝ)) gap C V bounds Fs.reverse
      (by intro F hmem j; exact hF F (List.mem_reverse.mp hmem) j) hp hprecision J hJ).withReplicaCount
        (2^g.a) (by simpa only [List.length_reverse] using g.hpower)
    let pubClass := gatherPublicationClass (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let keys := PackedExactBatch.ofCommonCoreClass_keys (A := prime+K)
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target
      (amortizedCoreWidth ct (Sizes.p n₀)) L (Real.sqrt (u : ℝ)) gap C V bounds Fs.reverse
      (by intro F hmem j; exact hF F (List.mem_reverse.mp hmem) j) hp hprecision J hJ
    let runTime := initializedPublishedRunTime F n₀ ct cV cD (Sizes.p n₀) u (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
    let runStock := initializedPublishedRunStock Cstock Cprog n₀ ct cV cD (Sizes.p n₀) (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
    let runProg : Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U := (inputTableClassProgram rg masters widthMaster zeroMaster (initializedClassProgram (fullExposedClassBank physicalBank) src
          (.seq g.program (inputClassProgram (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj) b rg))))
    let origins := (coreSubsetPublicationWindows (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      pubClass.length g.hwidth pubClass.indices pubClass.sublist).origins
    let a := Nat.clog 2 indices.length
    let Vpub := g.D
    let output := header (T+solverRegisterCount) .output
    let pubSrc := publication (T+solverRegisterCount)
    ∀ (ambient : Fin (2^g.a) → List (Fin (prime+K+4)))
    (_hambient : ∀ j, (ambient j).length = Sizes.s n₀ i*W)
    (outputTail : List (Fin (prime+K+4)))
    (_pubInput : PublicationCallerReady (classCallerRegister ∘ pubSrc) (selectedPublicationPlacement physicalBank output) base)
    (_hdstBase : base.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail)
    (_hPublicationVolume : Sizes.s n₀ i*W < 2^Vpub),
    ∀ (rawSrc : Fin 11 → Fin T) (_hrawSrc : rawSrc 8 ≠ rawSrc 4)
    (widthSource : Fin (T+solverRegisterCount)) (recovery : Bool) (_hAlphabet : 96 ≤ prime+K)
    (d : ℝ) (_hst : Sizes.s n₀ i < Sizes.t n₀ i) (_huPositive : 1 ≤ u)
    (_hwidth : 8*Sizes.p n₀ ≤ 2^u)
    (_hθ : 1/(4*(Sizes.p n₀ : ℝ)) ≤ (Sizes.t n₀ i : ℝ)/Sizes.s n₀ i-1)
    (_hgap : (1 : ℝ)/4 ≤ d*((Sizes.t n₀ i : ℝ)/Sizes.s n₀ i-1))
    (_hbudget : (u : ℝ)*d ≤ Sizes.p n₀)
    (_hband : PhaseCellBand.width (Sizes.p n₀) u ≤ Sizes.s n₀ i)
    (_hpad : 2*((Sizes.s n₀ i/(Sizes.t n₀ i-Sizes.s n₀ i)+1)-2*PhaseCellBand.width (Sizes.p n₀) u) ≤
      2^haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)+1)
    (_hroom : 3*amortizedCoreWidth ct (Sizes.p n₀) < Sizes.s n₀ i)
    (_hr : 0 < radius) (_hrw : radius ≤ amortizedCoreWidth ct (Sizes.p n₀))
    (_hW : 2*Sizes.p n₀+13 ≤ W) (_hvolume : Sizes.s n₀ i*W < 2^D)
    (X Y : (ZMod (Sizes.s n₀ i) → GaussianInt) → ZMod (Sizes.s n₀ i) → ℝ)
    (_hX : ∀ F ∈ Fs, Solves (realMatrix (Sizes.s n₀ i) (Sizes.t n₀ i) (Sizes.p n₀) u) Finset.univ (X F)
      (fun j => ((1/2 : ℂ)*value (Sizes.p n₀) (F j)).re))
    (_hY : ∀ F ∈ Fs, Solves (realMatrix (Sizes.s n₀ i) (Sizes.t n₀ i) (Sizes.p n₀) u) Finset.univ (Y F)
      (fun j => ((1/2 : ℂ)*value (Sizes.p n₀) (F j)).im))
    (_ready : BoundaryCallerReady rawSrc widthSource (Sizes.p n₀) u
      (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i) W D radius
      (amortizedCoreWidth ct (Sizes.p n₀)) Fs base)
    (_hboundaryPush : mnProgPush ((callerFullLineProducer T Q b.hR b.hQ).gridProgram
      (P := P) (U := U) (A := prime+K) recovery) ≤ Cprog),
    let geometryCost := PublicationGeometryControls.timeCost Vpub (Sizes.s n₀ i) L radius
    let retireGeometryCost := 2*((L-2*radius)+Sizes.s n₀ i)+5
    let dimensionCost := PackedTranspose.publicationDimensionsTimeCost g.a indices.length
    let retireDimensionCost := 2*(g.a+a+2^a)+7
    let metadata := PackedTranspose.publicationHeaderVolume a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) indices.length
    let originCost := preparedCoreOriginsCost Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let properTime := initializedPublishedTime setup.timeCost runTime (geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ) setup.retireCost
    let properStock := (setup.stock+(runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass))))))
    let properProgram : Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U := (.seq setup.program (.seq (publishedClassProgram runProg g.routeSrc pubSrc (physicalBank (.recovery (.control .result))) output hstates) setup.retire))
    ∃ rows : batch.Rows,
    let properLines := List.ofFn (fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j))
    let M : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K) :=
      {base with R := Function.update base.R (fullHeader _ .output) (properLines.flatten++outputTail)}
    let B := inverseCallerWordWidth (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
    let F := callerPreparedBoundaryState widthSource (Sizes.p n₀) (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) M
    let producer := callerFullLineProducer T Q b.hR b.hQ
    let r := fullLineGridRecord (A := prime+K) (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i) Fs
    let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
    let solveTime := setupTime (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i) Fs.length+
      ((r.gridCost (Sizes.p n₀) (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (Sizes.t n₀ i) producer.gridWork+22*tape.length+26)+(2*(∑ i, (r.words i).length)+607))
    let solveStock := setupStock (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i) Fs.length+(31*tape.length+9+(Cprog+1)*producer.gridStock (Sizes.p n₀) (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (Sizes.t n₀ i) r)
    let volume := r.inputs.length*(Sizes.s n₀ i)*(2*(Sizes.p n₀)+13)
    let generateTime := ((2*(Sizes.p n₀)+13)*(4*D+10)+4*D+8)+boundaryCountExportCost D (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) (2*(Sizes.p n₀)+13)+(2*D+2)
    let generateStock := 2*(4*D+4)+3*boundaryCountExportCost D (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) (2*(Sizes.p n₀)+13)
    let prepareTime := (4*(Sizes.p n₀)+5)+(generateTime+((4*B+5)+((solveTime+(242*volume+45))+(2*B+3))))
    let prepareStock := 13*(4*(Sizes.p n₀)+5)+(generateStock+(2*(4*B+5)+(solveStock+(480*volume+86))))
    let pairs := boundarySeamMasterCopies (boundaryArchiveSource (T+solverRegisterCount))
      (boundaryArchiveDestination (T+solverRegisterCount))
      (seamMasterSources (T+solverRegisterCount) (fun i => solverSource (rawSrc i)) widthSource)
    let loadCost := (pairs.map (fun pair => 6*(F.R pair.1).length+6)).sum+1
    let retireCost := 2*(pairs.map (fun pair => (F.R pair.1).length)).sum+2*pairs.length+1
    let clearCost := 2*((callerPreparedTemporaryHeaders (T+solverRegisterCount)).map (fun i => (F.R i).length)).sum+
      2*(callerPreparedTemporaryHeaders (T+solverRegisterCount)).length+1
    let publicationTime := (loadCost+(3*boundarySeamBudget r.inputs.length D (Sizes.s n₀ i) W+1)+retireCost)+clearCost
    let publicationStock := 2*loadCost+13*boundarySeamBudget r.inputs.length D (Sizes.s n₀ i) W
    ∃ finalLines : List (List (Fin ((prime+K)+4))),
      List.Forall₂ (fun target line => line.length = (Sizes.s n₀ i)*W ∧
        (∀ i : ZMod (Sizes.s n₀ i), ‖pairedCellRead (Sizes.p n₀) W line i‖ ≤ 1) ∧
        (∀ i : ZMod (Sizes.s n₀ i), ‖pairedCellRead (Sizes.p n₀) W line i-target i‖ ≤ 3/(2:ℝ)^(Sizes.p n₀)))
        (seamPublicationTargets (Sizes.p n₀) r (fun _ => J)) finalLines ∧
      ∃ v', ∃ m : ℕ, v'.user = v.user ∧ (m : ℝ) ≤ properTime+((prepareTime+publicationTime : ℕ) : ℝ) ∧
        mnSize (mk v' {base with R := Function.update base.R (fullHeader _ .output) (finalLines.flatten++outputTail)}) =
          mnSize (mk v base) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v base)+depth+max properStock (prepareStock+publicationStock)) depth
          (.seq properProgram (callerBoundaryCompletion rawSrc b.hR b.hQ widthSource recovery)) (mk v base) m
          (mk v' {base with R := Function.update base.R (fullHeader _ .output) (finalLines.flatten++outputTail)}) := by
  intro physicalBank physicalInj
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedInitializedPublishedClassRun_exec
    (body := body) (solverSource ∘ bank) ((Fin.castAdd_injective _ _).comp hinj) b hstates ct cV cD
  refine ⟨F,hF,Cstock,?_⟩
  filter_upwards [hclass] with n₀ hn
  intro h i _ _ u target L hu htarget gap C V bounds Fs hFs
  intro B W radius indices D Cprog depth Vg Vr replicaExp rg hpush hbody hwide hA
    v base borrowed input hgeometry hfit hbits movement hwords retained setup src masters caller
    widthMaster zeroMaster seed gatherInput g hExposeWidth hRouteWidth
    hMetadataFit hReplicaVolume hp hprecision J hJ batch pubClass keys runTime runStock runProg
    origins a Vpub output pubSrc ambient hambient outputTail pubInput hdstBase hPublicationVolume
    rawSrc hrawSrc widthSource recovery hAlphabet d hst huPositive hwidth hθ hgap hbudget hband hpad
    hroom hr hrw hW hvolume X Y hX hY ready hboundaryPush
    geometryCost retireGeometryCost dimensionCost retireDimensionCost metadata originCost
    properTime properStock properProgram
  obtain ⟨properVar,properSteps,outputs,rows,huser,htime,houtputs,hrows,hbank,hstock,he⟩ :=
    hn h i u target hu htarget (Real.sqrt (u : ℝ)) gap C V bounds Fs hFs D Cprog depth Vg Vr replicaExp
      hpush hbody hwide hA v base borrowed input hgeometry hfit hbits movement hwords retained caller
      gatherInput hExposeWidth hRouteWidth hMetadataFit hReplicaVolume hp hprecision J hJ
      ambient hambient outputTail pubInput hdstBase hPublicationVolume
  refine ⟨rows,?_⟩
  dsimp only
  obtain ⟨finalLines,haccuracy,v',m,huser',hm,hstock',he'⟩ := callerPublishedBoundaryExecution_exec
    rawSrc hrawSrc b.hR b.hQ widthSource D (amortizedCoreWidth ct (Sizes.p n₀)) movement.widthPositive
    hroom recovery hAlphabet hp hst huPositive hwidth hθ hgap hbudget hband hpad hprecision
    Fs hFs X Y hX hY J hJ W radius v base ready hW hvolume
    (PhaseCellBand.width (Sizes.p n₀) u) (localityDepth (Sizes.p n₀) target) pubClass hr hrw rfl
    _ hbank outputTail Cprog hboundaryPush hbody depth properProgram properSteps properStock properVar huser hstock he
  refine ⟨finalLines,haccuracy,v',m,huser',?_,hstock',he'⟩
  have hmR := (Nat.cast_le (α := ℝ)).mpr hm
  rw [Nat.cast_add] at hmR
  exact hmR.trans (add_le_add htime le_rfl)

end IntegerMultBounds.MathlibTM2.Cost
