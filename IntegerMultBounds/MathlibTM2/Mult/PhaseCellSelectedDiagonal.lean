module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedIntervalDiagonal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalDiagonalInput

/-! Actual selection, principal solve, cleanup, transfer and D-prime multiplication
on one physical state. Principal stability supplies the diagonal input radius. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry Routing.RetainedHaloTensor
noncomputable section
variable {ι : Type} [DecidableEq ι]
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def selectedDiagonal (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq (selectionSolve hR hQ) (placedDiagonal hQ)

theorem selectedDiagonal_exec
    (grid : ι → Axis) (retained : Finset ι) (f : (ι → ℕ) → GaussianInt)
    (before middle : List (Sum ι ι)) (aPrefix : ℕ) (i : ι) (hi : i ∈ retained) (k : ℕ)
    (hH : (grid i).H ≤ (grid i).N*(grid i).L) (hguard : (grid i).H ≤ k*(grid i).L)
    {W V a w n : ℕ} (hsource : a+n ≤ s)
    (hn : 0 < n) (hwide : a+n+2*((grid i).N*(grid i).L)*(a+n)+3*s < 2^W)
    (hwindow : ∀ j < n, (k*(grid i).L-(grid i).H) ≤ nearestNatural s ((grid i).N*(grid i).L) (a+j) ∧ nearestNatural s ((grid i).N*(grid i).L) (a+j) < (k*(grid i).L-(grid i).H)+((grid i).L+2*(grid i).H))
    (hwV : w < 2^V) (hspan : ((grid i).L+2*(grid i).H) < 2^V) (hvol : ((grid i).L+2*(grid i).H)*w < 2^V)
    (hVW : V ≤ W) (hA : 4 ≤ A) (hVpos : 0 < V)
    (tail : List (Fin (A+4)))
    (v : HS tapes Q A U) (S : Stacks tapes A)
    (hheaders : LocalSelectionHeaders A W V s ((grid i).N*(grid i).L) a (k*(grid i).L-(grid i).H) w n (embStk LocalRecoveryLayout.geometry (embStk selector S)))
    (hclock : (S.R (selector (LocalRecoveryLayout.batch 0))).length = ((middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod)) (hvolume : (S.R (selector (LocalRecoveryLayout.batch 1))).length = ((grid i).L+2*(grid i).H)*w)
    (hqueue : S.R (selector (LocalRecoveryLayout.batch 2)) = Routing.RetainedFieldBatch.batch A w grid retained before middle i aPrefix k f++tail)
    (harchive : S.R (selector (LocalRecoveryLayout.batch 3)) = []) (hacc : S.R (selector (LocalRecoveryLayout.batch 4)) = [])
    (hdst : S.R caller.archive = []) (hline : S.R (geometry 110) = [])
    (hN : (S.R (aux 7)).length = (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod)
    (hcountBlank : ∀ j ∈ [aux 6,caller.count,caller.saved,caller.tmp], S.R j = [])
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hAlphabet : 96 ≤ A)
    {p l u target : ℕ} {α d : ℝ}
    (recovery : RecoveryAxisBounds s ((grid i).N*(grid i).L) p u l α d)
    (hf : ∀ x, (∀ j, x j < (grid j).N*(grid j).L) → ‖value p (f x)‖ ≤ 1)
    (ha : a < s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (start coreRows radius : ℕ) (hleft : radius ≤ start)
    (haCore : a = start-radius) (hnCore : n = coreRows+2*radius)
    (hright : start+coreRows+radius ≤ s)
    (Bdiag Cdiag alpha : ℕ) (hp13 : 13 ≤ p) (halpha : 2 ≤ alpha)
    (hsquare : u = alpha^2) (hbudget : alpha^2 ≤ p) (hroom : 4*w+2 < 2^Bdiag)
    (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      LocalRecoveryLayout.diagonalMul LocalRecoveryLayout.diagonalMul_injective LocalRecoveryLayout.diagonal_tapes hQ
      (rsbCr LocalRecoveryLayout.diagonalRole .src .df .dst)) ≤ Cdiag) :
    let t := (grid i).N*(grid i).L
    let Fs := selectedRhsFields s
      ((Routing.RetainedFieldBatch.replicas grid retained before middle aPrefix).map
        (fun c => retainedTensorLine grid retained f c i))
    let hF := LocalRecoveryLayout.retainedReplicaRhs_bounded (s := s) grid retained f before middle aPrefix p i hf
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l stage 2
    let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
    let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
    let hRs := shiftedComplexComponents_bound p q hqp Fs hF
    let H := recovery.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
    let K := recovery.cyclicRightReplicaProblem stage 2 a n (by omega) Rs hRs
    ∀ (_ : 2*p+13 ≤ w) (_ : executionWidth p l stage 2 ≤ w),
    caller.InputContext H K w Fs.length radius coreRows S →
    LocalRecoveryLayout.DiagonalContext s t u p w Bdiag a radius coreRows Fs.length (embStk selector S) →
    S.R (selector LocalRecoveryLayout.diagonalQueue) = [] → S.R (aux 5) = [] →
    ∃ (vd : HS tapes Q A U) (I C F G O : Stacks tapes A) (J L : ReplicaHaloProblem s)
      (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (Ds : List (ZMod s → GaussianInt))
      (m steps nd : ℕ) (word : List (Fin (A+4))),
      let Z := retiredControls G
      let M := diagonalTransferState Z
      let N := (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod
      let selectorBill := LocalRecoveryLayout.preparedBulkSelectionCost W V ((grid i).L+2*(grid i).H) w n N+
        (archiveWidthSetupCost N n w+2*(n*w)+3)
      let numericBill := CyclicComplexCallerLayout.retiredTimeCost (A := A) (U := U) hR hQ
        (caller.inputTimeCost H K w Fs.length I+
          (caller.factorTimeCost s t p u a n C F+((4*(w+radius+coreRows)+13)+
            Cost.cyclicComplexCoreTimeCost H K p u l t a n target q w radius coreRows Rs.length Fs.length)))
        (Fs.length*n*w)
      let selectionStock := 3*LocalRecoveryLayout.preparedBulkSelectionCost W V ((grid i).L+2*(grid i).H) w n N+
        2*archiveWidthSetupCost N n w
      let numericStock := caller.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
        (executionWidth p l stage 2) w B.card Rs.length Fs.length radius coreRows I C F
      let diagonalStock := 16*LocalRecoveryLayout.diagonalPreparationCost (embStk selector M) Bdiag p w u t a radius coreRows+
        (2*bulkSelectionCountsCost Fs.length coreRows w+(2*(6*(coreRows*w)+6)+realWeightWorkspace Cdiag w coreRows))
      let packet := Ds.reverse.flatMap (fun D => cstream A w
        (packedInterval (a+radius) coreRows (diagonalProduct s t alpha p D)))
      vd.user = v.user ∧ Ds.length = Fs.length ∧
      m ≤ selectorBill ∧ steps ≤ numericBill ∧
      nd ≤ 4*word.length+4+
        LocalRecoveryLayout.completeDiagonalBatchCost (embStk selector M) Bdiag p w u t a radius coreRows Fs.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        ((selectionStock+numericStock)+diagonalStock)) 0
        (selectedDiagonal hR hQ) (mk v S) (m+steps+retireControlsCost G+nd) (mk vd O) ∧
      (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) ∧
      PackedIntervalOutput p w (a+radius) coreRows
        ((Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i)).reverse.map
          (fun z i => (dPrime s t (alpha : ℝ) i : ℂ)*z i))
        (6/(2 : ℝ)^p+(2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p)) packet ∧
      O.R (aux 5) = [] ∧ O.R (selector LocalRecoveryLayout.diagonalQueue) = [] ∧
      O.R (selector (LocalRecoveryLayout.diagonalRole .dst)) = packet ∧
      O = {M with R := (Function.update (Function.update M.R (selector LocalRecoveryLayout.diagonalQueue) [])
        (selector (LocalRecoveryLayout.diagonalRole .dst)) packet)} ∧
      word.length = Fs.length*coreRows*w := by
  dsimp only
  intro hw hExecutionWidth hcontext diagContext hqueueBlank houtputBlank
  obtain ⟨vi,vf,vg,I,C,F,G,J,L,m,steps,word,hu,hug,heSelect,hselected,heNumeric,heWhole,hm,htime,
    hstock,hword,hbank,harchiveOut,hcert,hqueueOut,hendpoint,hclean,hleft,hrecovery,hlen⟩ :=
    selectionSolve_exec (body := body) grid retained f before middle aPrefix i hi k hH hguard hsource
      hn hwide hwindow hwV hspan hvol hVW hA hVpos tail v S hheaders hclock hvolume hqueue harchive
      hacc hdst hline hN hcountBlank hR hQ hAlphabet recovery hf ha hleftRoom hrightRoom
      start coreRows radius hleft haCore hnCore hright hw hExecutionWidth hcontext
  let t := (grid i).N*(grid i).L
  let Fs := selectedRhsFields s
    ((Routing.RetainedFieldBatch.replicas grid retained before middle aPrefix).map
      (fun c => retainedTensorLine grid retained f c i))
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let stage := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card) 2
  let q := executionPrecision p l stage 2
  have hpq : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  have hstart : a+radius = start := by omega
  have hcore : haloVertices s start (start+coreRows) ⊆ cyclicPrincipalVertices s a n := by
    intro j hj
    obtain ⟨hjL,hjR⟩ := (mem_haloVertices _ _ j).mp hj
    apply Finset.mem_union_left
    apply (mem_haloVertices _ _ j).mpr
    rw [min_eq_left (by omega : n ≤ s-a)]
    constructor <;> omega
  have hF := LocalRecoveryLayout.retainedReplicaRhs_bounded (s := s) grid retained f before middle aPrefix p i hf
  obtain ⟨y,hsol,hpacket,hmag⟩ := hcert.diagonal_targets (by omega) hpq recovery.hdom hcore hF
  let targets := Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i)
  let Z := retiredControls G
  have diagZ := diagonalContext_of_recovery_frame diagContext hleft hrecovery
  have htmpI : I.R caller.tmp = [] :=
    ((hselected.outside _ (by simp [caller,aux,port_injective.eq_iff])
      (fun r => selector_ne_aux r 4)).2).trans hcontext.tmp
  have htmpZ : Z.R caller.tmp = [] := by
    rw [retiredControls_off G (by simp [controlWords,caller,geometry,selector,aux,port_injective.eq_iff])]
    rw [hendpoint]
    simp only [Function.update_of_ne (by simp [caller,aux,port_injective.eq_iff] : caller.tmp ≠ aux 5),
      Function.update_of_ne (show caller.tmp ≠ caller.archive from
        (selector_ne_aux LocalRecoveryLayout.source 4).symm)]
    exact htmpI
  let : NeZero t := ⟨Nat.ne_of_gt (Nat.mul_pos (grid i).N_pos (grid i).L_pos)⟩
  obtain ⟨vd,Ds,O,nd,hDs,hud,hdtime,hdstock,hauxOut,hdqueue,hdword,hdendpoint,hdaccuracy⟩ :=
    placedDiagonal_exec (body := body) hQ hAlphabet u alpha Bdiag p w a radius coreRows
      (NeZero.pos s) recovery.hst.le (by omega) hp13 halpha hsquare hbudget (by omega) hroom
      targets _ word (by simpa only [hstart] using hpacket) (by omega)
      (publicationError_le_half p target (by omega)) (by simpa only [hstart] using hmag)
      Cdiag hpush vg Z [] (by simpa only [targets,List.length_map] using diagZ)
      ((hrecovery (.control .cropDst)).trans hqueueBlank)
      (by simpa only [houtputBlank,List.append_nil] using hword) htmpZ
  refine ⟨vd,I,C,F,G,O,J,L,y,Ds,m,steps,nd,word,hud.trans hug,?_,hm,htime,?_,?_,hsol,hdaccuracy,
    hauxOut,hdqueue,hdword,hdendpoint,hlen⟩
  · simpa only [targets,List.length_map] using hDs
  · simpa only [targets,List.length_map] using hdtime
  · have hwhole := mn_seq_within_add hstock hdstock
    simpa only [targets,List.length_map,selectedDiagonal] using hwhole

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
