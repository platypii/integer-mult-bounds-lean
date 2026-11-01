module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedReplicaCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedReplicaRecoveryCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRecoveryBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRecoveryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingRetainedHeaders

/-! Actual shared coupling followed by complete boundary solve and recovery.
The phase boundary supplies no assumed residual archive or recovery readiness. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

noncomputable def coupledReplicaRecoveryCaller (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 389 Q A U :=
  .seq (releasedReplicaCoupling replicaRecoveryCallerCoupling 247 248 hQ)
    (releasedReplicaRecoveryCaller hR hQ)

def coupledReplicaRecoveryCallerCost (H : ReplicaHaloProblem s) (target : ℕ) :=
  releasedReplicaCouplingCost H+releasedReplicaRecoveryCallerCost H target (12*H.band+1)

theorem coupledReplicaRecoveryCaller_exec (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target : ℕ) (columns : List (ZMod s → GaussianInt))
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) i)).re))
    (outputTail rhsTail raw resultTail : List (Fin (A+4))) (buffers : ReplicaLoopBuffers A)
    (v : HS 389 Q A U) (S : Stacks 389 A)
    (hcursor : ReplicaCouplingCursor H 247 248 outputTail rhsTail 0 S)
    (hheaders : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (hnative : embStk weightCacheCoreReg (embStk replicaRecoveryCallerInterior.solver S) =
      releasedCellBank [] raw resultTail S.inp S.out)
    (hfactor : ReplicaBoundaryFactorData H target columns
      (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg S)))
    (hmasters : CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) (embStk replicaRecoveryCallerCoupling.bank S))
    (hstage : (S.R (replicaRecoveryCallerCoupling.bank 118)).length = H.stage+1)
    (hlevel : (S.R (replicaRecoveryCallerCoupling.bank 120)).length = H.l)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]),
      S.R (replicaRecoveryCallerCoupling.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167],
      S.R (replicaRecoveryCallerCoupling.bank k) = [])
    (hpage : S.R (replicaRecoveryCallerCoupling.bank 138) = [])
    (hclean : ∀ k ∈ ([129,131,133,134,136,153] : List (Fin 242)),
      (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg S)).R k = [])
    (hleft : ∀ k : Fin 255, S.L (replicaRecoveryCallerWorkerReg k) = [])
    (hprivate : ∀ k : Fin 255, 242 ≤ k.val → S.R (replicaRecoveryCallerWorkerReg k) = [])
    (hqueue : S.R 388 = []) (hcontroller : S.R 387 = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ coupledReplicaRecoveryCallerCost H target ∧
      Exec body (coupledReplicaRecoveryCaller hR hQ) (mk v S) n (mk v' F) ∧
      F.R 387 = [] ∧ F.R 121 = S.R 121 ∧ F.R 125 = [] ∧ F.R 388 = [] ∧
      RecoveredReplicaArchive H target X ((embStk replicaRecoveryCallerReg S).R 125)
        (embStk replicaRecoveryCallerWorkerReg F) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk replicaRecoveryCallerNativeReg F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk replicaRecoveryCallerWorkerReg F)) ∧
      ReplicaBoundaryFactorData H target columns
        (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg F)) := by
  have houtput (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ (247 : Fin 389) := by
    intro he
    have hv := congrArg (fun k : Fin 389 => k.val) he
    change k.val = 247 at hv
    have hk := k.isLt
    omega
  have hrhs (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ (248 : Fin 389) := by
    intro he
    have hv := congrArg (fun k : Fin 389 => k.val) he
    change k.val = 248 at hv
    have hk := k.isLt
    omega
  have hbout (k : Fin 168) : replicaRecoveryCallerCoupling.bank k ≠ 247 := by
    rw [replicaRecoveryCallerCoupling_bank]
    exact (replicaRecoveryCallerReg_outputs_disjoint _).1
  have hbrhs (k : Fin 168) : replicaRecoveryCallerCoupling.bank k ≠ 248 := by
    rw [replicaRecoveryCallerCoupling_bank]
    exact (replicaRecoveryCallerReg_outputs_disjoint _).2
  obtain ⟨v₁,J,n₁,Ds,hu₁,hn₁,he₁,h122,hout,hrhsTail,hready,hmeta,hL,hinp,houtTape,hframe,
    hlen,harchive,hgood,hpageJ,hcount,hrows,hfreshJ,hbounds,hgenerated,hshared⟩ :=
    releasedReplicaCoupling_exec (body := body) H replicaRecoveryCallerCoupling 247 248
      houtput hrhs hbout hbrhs (by decide) hQ hA hspan horigin
      outputTail rhsTail raw resultTail buffers v S hcursor hheaders hnative hblank hfresh
  rw [replicaRecoveryCallerCoupling_native_view] at hready hgenerated
  have hsharedR (k : Fin 168) (hk : 117 ≤ k.val) (hnot : k ∉ replicaCouplingSetupPorts) :
      (embStk replicaRecoveryCallerNativeReg J).R (Fin.castLE (by decide) k) =
        (embStk replicaRecoveryCallerNativeReg S).R (Fin.castLE (by decide) k) := by
    simpa only [replicaRecoveryCallerCoupling_right] using hshared k hk hnot
  have hfreshNative (k : Fin 168) (hk : k ∈ [(127 : Fin 168),143,166,158,135,167]) :
      (embStk replicaRecoveryCallerNativeReg J).R (Fin.castLE (by decide) k) = [] := by
    simpa only [replicaRecoveryCallerCoupling_right] using hfreshJ k hk
  have hheadersJ : ReplicaRecoveryRhsHeaders H replicaRecoveryCallerInterior.gather buffers J := by
    apply (hheaders.recovery_rhs H _ buffers S).of_archive_frame H _ buffers S J
    intro k hk
    apply hframe _ (fun i => replicaRecoveryCallerCoupling.bank_gather_disjoint i k)
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨houtput k,hrhs k,replicaRecoveryCallerInterior.gather_injective.ne hk⟩
  have hext := replicaRecoveryCallerCoupling_extension_frame hframe
  have hretained : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth H.wordWidth
      (embStk packedRecoveryRuntimeReg (embStk replicaRecoveryCallerNativeReg J)) := by
    rw [replicaRecoveryCallerCoupling_runtime_view]
    apply PackedHaloRetainedHeaders.of_coupling_setup hmasters hstage hlevel
    · simpa only [Nat.add_sub_cancel_left] using hmeta
    · exact hshared
  have hprivateJ (k : Fin 255) (hk : 242 ≤ k.val) : J.R (replicaRecoveryCallerWorkerReg k) = [] := by
    exact (hext (Fin.castLE (by decide) k) (by change 168 ≤ k.val; omega) (by
      intro he; have hv := congrArg (fun k : Fin 259 => k.val) he
      have hi := k.isLt; change k.val = 257 at hv; omega)).trans (hprivate k hk)
  have hleftJ (k : Fin 255) : J.L (replicaRecoveryCallerWorkerReg k) = [] := by
    rw [hL]; exact hleft k
  obtain ⟨hdata,hsharedBank⟩ :
      ReplicaBoundaryFactorData H target columns
        (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg J)) ∧
      ReplicaRecoverySharedBank H (12*H.band+1) (embStk replicaRecoveryCallerNativeReg J) := by
    refine hfactor.coupling_recovery_bank H target columns ?_ ?_ ?_ ?_ hretained ?_ hclean ?_ ?_ ?_ ?_ ?_
    · exact congrArg (fun L => L ∘ (replicaRecoveryCallerNativeReg ∘ packedBoundaryRecoveryBase)) hL
    · intro i
      exact (hready.clean i).2
    · exact hsharedR 119 (by decide) (by decide)
    · intro k hk h238
      exact hext (Fin.castLE (by decide) k) hk (by
        intro he; have hv := congrArg (fun k : Fin 259 => k.val) he
        have hi := k.isLt; change k.val = 257 at hv; omega)
    · intro k hk
      exact ⟨hleftJ (Fin.castLE (by decide) k),hprivateJ (Fin.castLE (by decide) k) hk⟩
    · intro k hk
      have hlow : k.val < 168 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
        norm_num at hk
        omega
      apply hsharedR ⟨k.val,hlow⟩
      · change 117 ≤ k.val
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
        norm_num at hk
        omega
      · simp only [replicaCouplingSetupPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
        norm_num at hk ⊢
        omega
    · intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact hfreshNative 127 (by decide)
      · exact hfreshNative 135 (by decide)
      · exact hfreshNative 143 (by decide)
      · exact hfreshNative 158 (by decide)
      · exact hfreshNative 166 (by decide)
    · rw [replicaRecoveryCallerCoupling_right] at hrows
      exact hrows
    · rw [hpage,List.append_nil,replicaRecoveryCallerCoupling_right] at hpageJ
      exact hpageJ
    · rw [replicaRecoveryCallerCoupling_right] at hcount
      exact hcount
  have hcost : releaseReplicaCouplingNativeCost (embStk replicaRecoveryCallerNativeReg J) ≤
      replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) := by
    apply releaseReplicaCouplingNativeCost_le_of_generated _ (2^15*H.p) H.precision H.wordWidth
      s H.t H.u H.band H.origin (H.origin+H.span) raw resultTail S.inp S.out
    intro i
    exact congrFun hgenerated i
  obtain ⟨v',F,n₂,hu₂,hn₂,he₂,h387,h121,h125,h388,h238,h93,houtputF,hcore,hphysical,
    h116,h167,hLF,hinpF,houtF,h110,h132,hpagesF⟩ :=
    releasedReplicaRecoveryCaller_exec (body := body) H hR hQ hA hp hwidth hspan hpad target
      (12*H.band+1) columns htarget hdata.prepared hdata.error X hX Ds ⟨hlen,hgood⟩ buffers v₁ J
      hheadersJ harchive ((hext 258 (by decide) (by decide)).trans hqueue)
      ((hext 255 (by decide) (by decide)).trans hcontroller)
      (by intro i; exact (hleftJ _).trans (hleftJ _).symm)
      hdata.pages (by intro i hi; exact hprivateJ i (by omega)) hsharedBank hcost
      (hfreshNative 167 (by decide))
  refine ⟨v',F,n₁+n₂,hu₂.trans hu₁,by unfold coupledReplicaRecoveryCallerCost; omega,
    Exec.seq he₁ he₂,h387,?_,h125,h388,?_,hcore,hphysical,?_⟩
  · apply h121.trans
    exact hframe _ (fun i => replicaRecoveryCallerCoupling.bank_gather_disjoint i 121) (by decide)
  · have htail := hsharedR 125 (by decide) (by decide)
    change (embStk replicaRecoveryCallerReg J).R 125 = (embStk replicaRecoveryCallerReg S).R 125 at htail
    rw [htail] at houtputF
    exact houtputF
  · exact ⟨hdata.prepared,hdata.error,hpagesF _ _ _ hdata.pages,hcore.bank⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
