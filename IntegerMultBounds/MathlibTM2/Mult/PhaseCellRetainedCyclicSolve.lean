module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedRetainedSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicRetirement

/-! The computed retained tensor batch is selected and solved on one physical
bank. No intermediate execution or numerical solution is supplied. -/
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

def selectionSolve (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P tapes Q A U :=
  .seq (.seq selectionCount (caller.retiredProgram (aux 5) hR hQ)) retireControls

theorem selectionSolve_exec
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
    (hright : start+coreRows+radius ≤ s) :
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
    ∃ (vi vf vg : HS tapes Q A U) (I C F G : Stacks tapes A)
      (J L : ReplicaHaloProblem s) (m steps : ℕ) (word : List (Fin (A+4))),
      vi.user = v.user ∧ vg.user = v.user ∧
      Exec body selectionCount (mk v S) m (mk vi I) ∧
      SelectedInput Fs a n w S I ∧
      Exec body (caller.retiredProgram (aux 5) hR hQ) (mk vi I) steps (mk vf G) ∧
      Exec body (selectionSolve hR hQ) (mk v S) (m+steps+retireControlsCost G) (mk vg (retiredControls G)) ∧
      m ≤ LocalRecoveryLayout.preparedBulkSelectionCost W V ((grid i).L+2*(grid i).H) w n
        (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod+
        (archiveWidthSetupCost (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod n w+2*(n*w)+3) ∧
      steps ≤ CyclicComplexCallerLayout.retiredTimeCost (A := A) (U := U) hR hQ
        (caller.inputTimeCost H K w Fs.length I+
          (caller.factorTimeCost s t p u a n C F+((4*(w+radius+coreRows)+13)+
            Cost.cyclicComplexCoreTimeCost H K p u l t a n target q w radius coreRows Rs.length Fs.length)))
        (Fs.length*n*w) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        ((3*LocalRecoveryLayout.preparedBulkSelectionCost W V ((grid i).L+2*(grid i).H) w n
          (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod+
          2*archiveWidthSetupCost (middle.map (Routing.RetainedTensorEnumeration.width grid retained)).prod n w)+
          caller.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
            (executionWidth p l stage 2) w B.card Rs.length Fs.length radius coreRows I C F)) 0
        (selectionSolve hR hQ) (mk v S) (m+steps+retireControlsCost G) (mk vg (retiredControls G)) ∧
      (retiredControls G).R (aux 5) = word++S.R (aux 5) ∧
      (∀ j, (retiredControls G).L (caller.bank j) = [] ∧ (retiredControls G).R (caller.bank j) = []) ∧
      (retiredControls G).R caller.archive = [] ∧
      PackedPrincipalOutput (realMatrix s t p u) (cyclicPrincipalVertices s a n)
        p q w target start coreRows Fs word ∧
      (retiredControls G).R (selector (LocalRecoveryLayout.batch 2)) = S.R (selector (LocalRecoveryLayout.batch 2)) ∧
      G = {I with R := Function.update (Function.update I.R caller.archive []) (aux 5) (word++I.R (aux 5))} ∧
      (∀ r ∈ controlWords, (retiredControls G).R r = []) ∧
      (retiredControls G).L = S.L ∧
      (∀ j, (retiredControls G).R (selector (LocalRecoveryLayout.recovery j)) =
        S.R (selector (LocalRecoveryLayout.recovery j))) ∧
      word.length = Fs.length*coreRows*w := by
  dsimp only
  intro hw hExecutionWidth hcontext
  obtain ⟨vi,I,m,hu,hm,he,hselected,hwithin⟩ := selectionCount_exec (body := body)
    grid retained f before middle aPrefix i hi k hH hguard hsource hn hwide hwindow hwV hspan hvol
    hVW hA hVpos tail v S hheaders hclock hvolume hqueue harchive hacc hdst hline hN hcountBlank
  let Fs := selectedRhsFields s
    ((Routing.RetainedFieldBatch.replicas grid retained before middle aPrefix).map
      (fun c => retainedTensorLine grid retained f c i))
  have hinput := hselected.toPackedInput hcontext
  have hF := LocalRecoveryLayout.retainedReplicaRhs_bounded (s := s) grid retained f before middle aPrefix p i hf
  obtain ⟨J,L,vm,vf,C,F,R,G,runSteps,steps,word,huf,hseed,hvalues,hprofile,hrun,hsteps,hclear,
    htime,hstock,hex,hword,hblank,harchiveOut,hcert,hstreams,hleftArchive,hendpoint,hlen,hsmall,hvolumeOut,hsize,hframe⟩ :=
    caller.retiredProgram_interval_exec (body := body) (aux 5)
      (by intro j; simp [caller,numeric,aux,port_injective.eq_iff])
      (selector_ne_aux _ _).symm hR hQ hAlphabet recovery ha (by omega) hleftRoom hrightRoom
      start coreRows radius hleft haCore hnCore hright Fs hF w hw hExecutionWidth vi I []
      hinput.bank hinput.seedL hinput.seedR (by simpa only [List.append_nil] using hinput.archive)
      hinput.count hinput.span hinput.controls hinput.saved hinput.tmp
  have haux : I.R (aux 5) = S.R (aux 5) :=
    (hselected.outside _ (by simp [caller,aux,port_injective.eq_iff]) (fun r => selector_ne_aux r 5)).2
  have hqueueNe : selector (LocalRecoveryLayout.batch 2) ≠ caller.archive := by
    exact selector_injective.ne (LocalRecoveryLayout.geometry_ne_batch 108 2).symm
  have hqueueOut := (hframe (selector (LocalRecoveryLayout.batch 2)) hqueueNe
    (selector_ne_aux _ _) (fun j => (selector_ne_numeric _ j).symm)).2
  obtain ⟨vg,hug,hclean⟩ := retireControls_exec (body := body) vf G 0
  have hwhole := mn_seq_within_add (hwithin 0) hstock
  refine ⟨vi,vf,vg,I,C,F,G,J,L,m,steps,word,hu,hug.trans (huf.trans hu),he,hselected,hex,
    Exec.seq (Exec.seq he hex) hclean.toExec,hm,htime,?_,?_,?_,?_,hcert,?_,hendpoint,?_,?_,?_,hlen⟩
  · exact mn_seq_within_no_growth hwhole hclean
  · rw [retiredControls_off G aux5_not_controlWords]
    exact hword.trans (congrArg (word ++ ·) haux)
  · intro j
    exact ⟨(hblank j).1,(retiredControls_off G (numeric_not_controlWords j)).trans (hblank j).2⟩
  · exact (retiredControls_off G archive_not_controlWords).trans harchiveOut
  · exact (retiredControls_off G queue_not_controlWords).trans (hqueueOut.trans hselected.queue)
  · intro r hr
    exact retiredControls_on G hr
  · exact hleftArchive.trans hselected.left
  · intro j
    rw [retiredControls_off G (recovery_not_controlWords j)]
    have harchive : selector (LocalRecoveryLayout.recovery j) ≠ caller.archive :=
      selector_injective.ne (LocalRecoveryLayout.geometry_ne_recovery 108 j).symm
    exact ((hframe _ harchive (selector_ne_aux _ _) (fun r => (selector_ne_numeric _ r).symm)).2).trans
      (hselected.recovery j)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.RetainedCyclicLayout
