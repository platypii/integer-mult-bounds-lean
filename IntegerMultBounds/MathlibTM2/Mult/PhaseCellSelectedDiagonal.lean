module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedIntervalDiagonal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishRetainedInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoreRetainedClock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceRetainedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalDiagonalInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalDiagonalB0Budget

/-! Actual selection, principal solve, cleanup, transfer and D-prime multiplication
on one physical state. Principal stability supplies the diagonal input radius. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
  Routing.RetainedHaloTensor
noncomputable section
variable {ι : Type} [DecidableEq ι]
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P tapes Q A U}

def selectedDiagonal (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq (.seq (.seq (selectionSolve hR hQ) (placedDiagonal hQ)) publishDiagonal) advanceRetainedBatch

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
    let _ : NeZero t := ⟨Nat.ne_of_gt (Nat.mul_pos (grid i).N_pos (grid i).L_pos)⟩
    let fields := (Routing.RetainedFieldBatch.replicas grid retained before middle aPrefix).map
      (fun c => retainedTensorLine grid retained f c i)
    let Fs := selectedRhsFields s fields
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
    ∃ (va : HS tapes Q A U) (I C F G O published advanced : Stacks tapes A) (J L : ReplicaHaloProblem s)
      (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (Ds : List (ZMod s → GaussianInt))
      (m steps nd na : ℕ) (word : List (Fin (A+4))),
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
      let advanceBill := retireCountedLineCost N (localLength grid retained i*w)
      let packet := Ds.reverse.flatMap (fun D => cstream A w
        (packedInterval (a+radius) coreRows (diagonalProduct s t alpha p D)))
      va.user = v.user ∧ Ds.length = Fs.length ∧
      m ≤ selectorBill ∧ steps ≤ numericBill ∧
      nd ≤ 4*word.length+4+
        LocalRecoveryLayout.completeDiagonalBatchCost (embStk selector M) Bdiag p w u t a radius coreRows Fs.length ∧
      na ≤ advanceBill ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        (((selectionStock+numericStock)+diagonalStock)+3*advanceBill)) 0
        (selectedDiagonal hR hQ) (mk v S) (m+steps+retireControlsCost G+nd+(4*(Fs.length*coreRows*w)+4)+na) (mk va advanced) ∧
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
      advanced.R outputArchive = packet++S.R outputArchive ∧
      advanced.R (selector (LocalRecoveryLayout.diagonalRole .dst)) = [] ∧
      published = {O with R := (Function.update
        (Function.update O.R (selector (LocalRecoveryLayout.diagonalRole .dst)) [])
        outputArchive (packet++O.R outputArchive))} ∧
      advanced.R (selector (LocalRecoveryLayout.batch 2)) = tail ∧
      advanced = {published with R := Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail} ∧
      (∀ r ∈ [caller.count,caller.saved,caller.tmp], advanced.R r = []) ∧
      advanced.R (aux 7) = S.R (aux 7) ∧
      (∀ j : Fin 6, advanced.R (selector (LocalRecoveryLayout.batch j)) =
        if j = 2 then tail else if j = 0 then [] else S.R (selector (LocalRecoveryLayout.batch j))) ∧
      advanced.L = S.L ∧
      (∀ j, advanced.L (caller.bank j) = [] ∧ advanced.R (caller.bank j) = []) ∧
      LocalRecoveryLayout.DiagonalFresh (embStk selector advanced) ∧
      ClockRestoreInput N advanced ∧
      word.length = Fs.length*coreRows*w ∧
      ∀ (localityTarget : ℕ), radius = localityDepth p localityTarget*PhaseCellBand.width p u →
        start = cut s t (grid i).L k → coreRows = rows s t (grid i).L k →
        localityDepth p localityTarget*PhaseCellBand.width p u ≤ cut s t (grid i).L k →
        cut s t (grid i).L (k+1)+localityDepth p localityTarget*PhaseCellBand.width p u ≤ s →
        ∀ (inverse : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)),
        inverse ∘L PhaseCellOperator.exact s t (alpha : ℝ) = 1 →
        PackedIntervalOutput p w (a+radius) coreRows
          (fields.reverse.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*
            resampB₀ s t (alpha : ℝ) inverse (fun i => value p (F i)) i))
          ((6/(2 : ℝ)^p+(2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p))+
            ((2/(2 : ℝ)^localityTarget)/(2 : ℝ)^inverseNormalizationShift p+
              (((32*(p : ℝ)^2/(2 : ℝ)^(45*p))/2)/(2 : ℝ)^inverseNormalizationShift p))) packet ∧
        (p+2 ≤ target → p+2 ≤ localityTarget →
          PackedUnitIntervalOutput p w (a+radius) coreRows
            (fields.reverse.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*
              resampB₀ s t (alpha : ℝ) inverse (fun i => value p (F i)) i)) (9/(2 : ℝ)^p) packet) := by
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
  let packet := Ds.reverse.flatMap (fun D => cstream A w
    (packedInterval (a+radius) coreRows (diagonalProduct s t alpha p D)))
  have packetLen : packet.length = Fs.length*coreRows*w := by
    simpa only [targets,List.length_map,List.length_reverse] using hdaccuracy.length (by omega)
  have hAuxO (j : Fin 9) (hj2 : j ≠ 2) (hj5 : j ≠ 5) : O.R (aux j) = S.R (aux j) := by
    have hAuxI : I.R (aux j) = S.R (aux j) :=
      (hselected.outside _ (by simp [caller,aux,port_injective.eq_iff,hj2])
        (fun r => selector_ne_aux r j)).2
    have hAuxG : G.R (aux j) = S.R (aux j) := by
      rw [hendpoint]
      simp only [Function.update_of_ne (by simp [aux,port_injective.eq_iff,hj5] : aux j ≠ aux 5),
        Function.update_of_ne (show aux j ≠ caller.archive from (selector_ne_aux LocalRecoveryLayout.source j).symm)]
      exact hAuxI
    have hAuxZ : Z.R (aux j) = S.R (aux j) :=
      (retiredControls_off G (by simp [controlWords,caller,geometry,selector,aux,port_injective.eq_iff,hj2])).trans hAuxG
    rw [hdendpoint]
    simp only [Function.update_of_ne (selector_ne_aux (LocalRecoveryLayout.diagonalRole .dst) j).symm,
      Function.update_of_ne (selector_ne_aux LocalRecoveryLayout.diagonalQueue j).symm,
      diagonalTransferState,Function.update_of_ne (by simp [aux,port_injective.eq_iff,hj5] : aux j ≠ aux 5)]
    exact hAuxZ
  have hArchiveO : O.R outputArchive = S.R outputArchive := hAuxO 8 (by decide) (by decide)
  have htmpO : O.R caller.tmp = [] :=
    (hAuxO 4 (by decide) (by decide)).trans hcontext.tmp
  have hBatchO (j : Fin 6) :
      O.R (selector (LocalRecoveryLayout.batch j)) = if j = 0 then [] else S.R (selector (LocalRecoveryLayout.batch j)) := by
    have hd : selector (LocalRecoveryLayout.batch j) ≠ selector (LocalRecoveryLayout.diagonalRole .dst) :=
      selector_injective.ne (LocalRecoveryLayout.batch_ne_recovery j _)
    have hq : selector (LocalRecoveryLayout.batch j) ≠ selector LocalRecoveryLayout.diagonalQueue :=
      selector_injective.ne (LocalRecoveryLayout.batch_ne_recovery j _)
    rw [hdendpoint]
    simp only [Function.update_of_ne hd,Function.update_of_ne hq,diagonalTransferState,
      Function.update_of_ne (selector_ne_aux (LocalRecoveryLayout.batch j) 5)]
    exact hqueueOut j
  have hCountO : O.R caller.count = [] := by
    rw [hdendpoint]
    simp only [Function.update_of_ne (show caller.count ≠ selector (LocalRecoveryLayout.diagonalRole .dst) from
        (selector_ne_aux _ 2).symm),
      Function.update_of_ne (show caller.count ≠ selector LocalRecoveryLayout.diagonalQueue from (selector_ne_aux _ 2).symm),
      diagonalTransferState,Function.update_of_ne (by simp [caller,aux,port_injective.eq_iff] : caller.count ≠ aux 5)]
    exact hclean _ (by simp [controlWords])
  obtain ⟨vp,hup,hpublish⟩ := publishDiagonal_exec (body := body) vd O packet hdword htmpO 0
  let published := {O with R := (Function.update
    (Function.update O.R (selector (LocalRecoveryLayout.diagonalRole .dst)) [])
    outputArchive (packet++O.R outputArchive))}
  rw [packetLen] at hpublish
  have hPublishedR (r : Fin tapes) (hd : r ≠ selector (LocalRecoveryLayout.diagonalRole .dst))
      (ha : r ≠ outputArchive) : published.R r = O.R r := by
    change Function.update (Function.update O.R _ []) outputArchive _ r = _
    rw [Function.update_of_ne ha,Function.update_of_ne hd]
  have hPublishedAux (j : Fin 9) (hj2 : j ≠ 2) (hj5 : j ≠ 5) (hj8 : j ≠ 8) :
      published.R (aux j) = S.R (aux j) :=
    (hPublishedR _ (selector_ne_aux _ j).symm (by simp [outputArchive,aux,port_injective.eq_iff,hj8])).trans
      (hAuxO j hj2 hj5)
  have hPublishedBatchAll (j : Fin 6) : published.R (selector (LocalRecoveryLayout.batch j)) =
      if j = 0 then [] else S.R (selector (LocalRecoveryLayout.batch j)) :=
    (hPublishedR _ (selector_injective.ne (LocalRecoveryLayout.batch_ne_recovery j _))
      (selector_ne_aux _ 8)).trans (hBatchO j)
  have hPublishedBatch (j : Fin 6) (hj : j ≠ 0) :
      published.R (selector (LocalRecoveryLayout.batch j)) = S.R (selector (LocalRecoveryLayout.batch j)) := by
    simpa only [hj,ite_false] using hPublishedBatchAll j
  have hblankPublished : ∀ r ∈ [caller.count,caller.saved,caller.tmp], published.R r = [] := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hPublishedR _ (selector_ne_aux _ 2).symm
        (by simp [outputArchive,aux,port_injective.eq_iff])).trans hCountO
    · exact (hPublishedAux 3 (by decide) (by decide) (by decide)).trans hcontext.saved
    · exact (hPublishedAux 4 (by decide) (by decide) (by decide)).trans hcontext.tmp
  obtain ⟨va,na,hua,hatime,hadvance⟩ := advanceRetainedBatch_exec (body := body)
    grid retained before middle i aPrefix k w f tail vp published
    ((congrArg List.length (hPublishedAux 7 (by decide) (by decide) (by decide))).trans hN)
    (by rw [hPublishedBatch 1 (by decide)]; simpa only [localLength,hi,ite_true] using hvolume)
    ((hPublishedBatch 2 (by decide)).trans hqueue) hblankPublished 0
  let advanced := {published with R := Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail}
  have hFinalLeftZ : advanced.L = Z.L := by
    change O.L = Z.L
    rw [hdendpoint]
    rfl
  have hFinalLeft : advanced.L = S.L := hFinalLeftZ.trans hleft
  have hFinalDst : advanced.R (selector (LocalRecoveryLayout.diagonalRole .dst)) = [] := by
    change Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail
      (selector (LocalRecoveryLayout.diagonalRole .dst)) = []
    rw [Function.update_of_ne (show selector (LocalRecoveryLayout.diagonalRole .dst) ≠ selector (LocalRecoveryLayout.batch 2) from
      selector_injective.ne (LocalRecoveryLayout.batch_ne_recovery 2 _).symm)]
    simp only [published,Function.update_of_ne (show selector (LocalRecoveryLayout.diagonalRole .dst) ≠ outputArchive from
      selector_ne_aux _ 8),Function.update_self]
  have hFinalBatch (j : Fin 6) : advanced.R (selector (LocalRecoveryLayout.batch j)) =
      if j = 2 then tail else if j = 0 then [] else S.R (selector (LocalRecoveryLayout.batch j)) := by
    change Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail
      (selector (LocalRecoveryLayout.batch j)) = _
    by_cases hj : j = 2
    · subst j
      simp only [Function.update_self,ite_true]
    · rw [Function.update_of_ne (selector_injective.ne (LocalRecoveryLayout.batch_injective.ne hj))]
      simp only [hj,ite_false]
      exact hPublishedBatchAll j
  have hFinalBank : ∀ j, advanced.L (caller.bank j) = [] ∧ advanced.R (caller.bank j) = [] := by
    intro j
    refine ⟨(congrFun hFinalLeftZ _).trans (hbank j).1,?_⟩
    have hq : numeric j ≠ selector (LocalRecoveryLayout.batch 2) := (selector_ne_numeric _ j).symm
    have hd : numeric j ≠ selector (LocalRecoveryLayout.diagonalRole .dst) := (selector_ne_numeric _ j).symm
    have hdq : numeric j ≠ selector LocalRecoveryLayout.diagonalQueue := (selector_ne_numeric _ j).symm
    have ha : numeric j ≠ outputArchive := by simp [outputArchive,numeric,aux,port_injective.eq_iff]
    have h5 : numeric j ≠ aux 5 := by simp [numeric,aux,port_injective.eq_iff]
    change advanced.R (numeric j) = []
    simp only [advanced,published,Function.update_of_ne hq,Function.update_of_ne ha,Function.update_of_ne hd]
    rw [hdendpoint]
    simp only [Function.update_of_ne hd,Function.update_of_ne hdq,diagonalTransferState,Function.update_of_ne h5]
    exact (hbank j).2
  have hFinalFresh : LocalRecoveryLayout.DiagonalFresh (embStk selector advanced) := by
    refine ⟨fun j => (congrFun hFinalLeft (selector j)).trans (diagContext.fresh.left j),?_⟩
    intro j
    by_cases hd : LocalRecoveryLayout.recovery (.work j) = LocalRecoveryLayout.diagonalRole .dst
    · change advanced.R (selector (LocalRecoveryLayout.recovery (.work j))) = []
      rw [hd]
      exact hFinalDst
    · have hd' : selector (LocalRecoveryLayout.recovery (.work j)) ≠ selector (LocalRecoveryLayout.diagonalRole .dst) :=
        selector_injective.ne hd
      have hb : selector (LocalRecoveryLayout.recovery (.work j)) ≠ selector (LocalRecoveryLayout.batch 2) :=
        selector_injective.ne (LocalRecoveryLayout.batch_ne_recovery 2 (.work j)).symm
      have hq : selector (LocalRecoveryLayout.recovery (.work j)) ≠ selector LocalRecoveryLayout.diagonalQueue := by
        simp [selector_injective.eq_iff,LocalRecoveryLayout.diagonalQueue,LocalRecoveryLayout.recovery_injective.eq_iff]
      have ha : selector (LocalRecoveryLayout.recovery (.work j)) ≠ outputArchive := selector_ne_aux _ 8
      have h5 : selector (LocalRecoveryLayout.recovery (.work j)) ≠ aux 5 := selector_ne_aux _ 5
      change advanced.R (selector (LocalRecoveryLayout.recovery (.work j))) = []
      simp only [advanced,published,Function.update_of_ne hb,Function.update_of_ne ha,Function.update_of_ne hd']
      rw [hdendpoint]
      simp only [Function.update_of_ne hd',Function.update_of_ne hq,diagonalTransferState,Function.update_of_ne h5]
      exact (hrecovery (.work j)).trans (diagContext.fresh.work j)
  have hFinalBlank : ∀ r ∈ [caller.count,caller.saved,caller.tmp], advanced.R r = [] := by
    intro r hr
    have hoff : r ≠ selector (LocalRecoveryLayout.batch 2) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals exact (selector_ne_aux _ _).symm
    change Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail r = []
    rw [Function.update_of_ne hoff]
    exact hblankPublished r hr
  have hFinalMaster : advanced.R (aux 7) = S.R (aux 7) := by
    change Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail (aux 7) = _
    rw [Function.update_of_ne (selector_ne_aux _ 7).symm]
    exact hPublishedAux 7 (by decide) (by decide) (by decide)
  have hRestore : ClockRestoreInput
      (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod advanced :=
    ⟨(congrArg List.length hFinalMaster).trans hN,
      by simpa only [show (0 : Fin 6) ≠ 2 by decide,ite_false,ite_true] using hFinalBatch 0,
      hFinalBlank caller.tmp (by simp)⟩
  refine ⟨va,I,C,F,G,O,published,advanced,J,L,y,Ds,m,steps,nd,na,word,hua.trans (hup.trans (hud.trans hug)),
    ?_,hm,htime,?_,hatime,?_,hsol,hdaccuracy,hauxOut,hdqueue,hdword,hdendpoint,?_,hFinalDst,rfl,?_,rfl,hFinalBlank,hFinalMaster,hFinalBatch,hFinalLeft,hFinalBank,hFinalFresh,hRestore,hlen,?_⟩
  · simpa only [targets,List.length_map] using hDs
  · simpa only [targets,List.length_map] using hdtime
  · have hwhole := mn_seq_within_add
      (mn_seq_within_no_growth (mn_seq_within_add hstock hdstock) hpublish) hadvance
    simpa only [targets,List.length_map,selectedDiagonal] using hwhole
  · change Function.update published.R (selector (LocalRecoveryLayout.batch 2)) tail outputArchive = _
    rw [Function.update_of_ne (show outputArchive ≠ selector (LocalRecoveryLayout.batch 2) from
      (selector_ne_aux _ 8).symm)]
    simp only [published,Function.update_self,hArchiveO]
    rfl
  · exact Function.update_self _ _ _
  · intro localityTarget hRadius hStart hRows hGuardL hGuardR inverse hInverse
    have hAlpha : (alpha : ℝ) = α := by
      have hNat : (u : ℝ) = (alpha : ℝ)^2 := by exact_mod_cast hsquare
      have hAlphaPos := recovery.hα
      have hNatPos : (0 : ℝ) < alpha := by exact_mod_cast (show 0 < alpha by omega)
      nlinarith only [hNat,hAlphaPos,hNatPos,recovery.hαu]
    have recoveryAlpha : RecoveryAxisBounds s t p u l (alpha : ℝ) d := by
      simpa only [hAlpha] using recovery
    have hOrigin : a = cut s t (grid i).L k-localityDepth p localityTarget*PhaseCellBand.width p u := by
      rw [hRadius,hStart] at haCore
      exact haCore
    have hSpan : n = rows s t (grid i).L k+2*(localityDepth p localityTarget*PhaseCellBand.width p u) := by
      rw [hRadius,hRows] at hnCore
      exact hnCore
    have hsolOwned := hsol
    change ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      (cyclicPrincipalVertices s a n) (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) at hsolOwned
    rw [hOrigin,hSpan] at hsolOwned
    have hpacketOwned := hdaccuracy
    rw [hstart,hStart,hRows] at hpacketOwned
    have hfields := LocalRecoveryLayout.retainedReplicaFields_bounded
      grid retained f before middle aPrefix p i hf
    have hresult := hpacketOwned.target_owned_B0 recoveryAlpha hpq (grid i).L k localityTarget
      hGuardL hGuardR _ hfields y hsolOwned inverse hInverse
    refine ⟨?_,?_⟩
    · simpa only [hstart,hStart,hRows] using hresult
    · intro htarget hlocality
      have herror := principalDiagonalB0_error_le_nine (j := inverseNormalizationShift p)
        (by omega : 4 ≤ p) htarget hlocality
      have hunit := hresult.b0_unit_fields recoveryAlpha (by omega) (by omega) (by omega)
        (by omega) _ hfields inverse hInverse herror
      simpa only [hstart,hStart,hRows] using hunit

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
