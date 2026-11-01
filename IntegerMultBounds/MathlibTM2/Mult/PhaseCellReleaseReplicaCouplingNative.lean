module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPlacement

/-! Retire the coupling-owned native arithmetic bank before recovery. Payload
ports survive, high shared pages stay fixed, and every erased symbol is paid. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def replicaCouplingNativePorts : List (Fin 248) :=
  (List.finRange 248).filter (fun k => decide (k.val < 117 ∧ k ≠ 93 ∧ k ≠ 110))

@[simp] theorem mem_replicaCouplingNativePorts (k : Fin 248) :
    k ∈ replicaCouplingNativePorts ↔ k.val < 117 ∧ k ≠ 93 ∧ k ≠ 110 := by
  simp [replicaCouplingNativePorts]

def releasedReplicaCouplingNative (S : Stacks 248 A) : Stacks 248 A :=
  {S with R := fun k => if k.val < 117 ∧ k ≠ 93 ∧ k ≠ 110 then [] else S.R k}

def releaseReplicaCouplingNative : Pr P 248 Q A U := clearWords replicaCouplingNativePorts

def releaseReplicaCouplingNativeCost (S : Stacks 248 A) :=
  2*(replicaCouplingNativePorts.map (fun k => (S.R k).length)).sum+2*replicaCouplingNativePorts.length+1

theorem releasedReplicaCouplingNative_high (S : Stacks 248 A) (k : Fin 248) (hk : 117 ≤ k.val) :
    (releasedReplicaCouplingNative S).R k = S.R k := by
  simp [releasedReplicaCouplingNative,show ¬ k.val < 117 by omega]

theorem releasedReplicaCouplingNative_blank (S : Stacks 248 A) (i : Fin 117) (h93 : i ≠ 93) (h110 : i ≠ 110) :
    (releasedReplicaCouplingNative S).R ⟨i.val,by omega⟩ = [] := by
  have h93' : (⟨i.val,by omega⟩ : Fin 248) ≠ 93 := by
    intro h; apply h93; exact Fin.ext (congrArg (fun k : Fin 248 => k.val) h)
  have h110' : (⟨i.val,by omega⟩ : Fin 248) ≠ 110 := by
    intro h; apply h110; exact Fin.ext (congrArg (fun k : Fin 248 => k.val) h)
  simp [releasedReplicaCouplingNative,i.isLt,h93',h110']

theorem releasedReplicaCouplingNative_bank {q w W N : ℕ} {S : Stacks 248 A}
    (hbank : PackedPreparedBank q w W N (embStk packedBoundaryRecoveryBase S)) :
    PackedPreparedBank q w W N (embStk packedBoundaryRecoveryBase (releasedReplicaCouplingNative S)) := by
  apply hbank.of_recovery_frame (F := embStk packedBoundaryRecoveryBase (releasedReplicaCouplingNative S)) rfl
  · intro i
    exact releasedReplicaCouplingNative_blank S ⟨i.val,by omega⟩ (by
      intro h; have hv := congrArg (fun k : Fin 117 => k.val) h; have hb := i.isLt; norm_num at hv; omega) (by
      intro h; have hv := congrArg (fun k : Fin 117 => k.val) h; have hb := i.isLt; norm_num at hv; omega)
  · exact releasedReplicaCouplingNative_high S 119 (by decide)
  · intro k hk h238
    apply releasedReplicaCouplingNative_high
    exact le_trans (by decide) hk

theorem releaseReplicaCouplingNative_exec (v : HS 248 Q A U) (S : Stacks 248 A) :
    ∃ v', v'.user = v.user ∧
      Exec body releaseReplicaCouplingNative (mk v S) (releaseReplicaCouplingNativeCost S)
        (mk v' (releasedReplicaCouplingNative S)) := by
  have hnd : replicaCouplingNativePorts.Nodup := (List.nodup_finRange 248).filter _
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) replicaCouplingNativePorts hnd v S
  exact ⟨v',hu,by simpa only [releaseReplicaCouplingNative,releaseReplicaCouplingNativeCost,
    releasedReplicaCouplingNative,mem_replicaCouplingNativePorts] using he⟩

theorem releaseReplicaCouplingNativeCost_eq_of_native_frame (S F : Stacks 248 A)
    (hframe : ∀ i : Fin 117, F.R ⟨i.val,by omega⟩ = S.R ⟨i.val,by omega⟩) :
    releaseReplicaCouplingNativeCost F = releaseReplicaCouplingNativeCost S := by
  have hmap : replicaCouplingNativePorts.map (fun k => (F.R k).length) =
      replicaCouplingNativePorts.map (fun k => (S.R k).length) := by
    apply List.map_congr_left
    intro k hk
    have hlow := (mem_replicaCouplingNativePorts k).mp hk
    exact congrArg List.length (hframe ⟨k.val,hlow.1⟩)
  unfold releaseReplicaCouplingNativeCost
  rw [hmap]


theorem releaseReplicaCouplingNativeCost_eq_of_coupling_frame {T : ℕ}
    {plan : ReplicaInteriorPlacement T} (placement : ReplicaCouplingPlacement plan)
    (e : Fin 248 → Fin T)
    (hnative : ∀ i : Fin 117, e ⟨i.val,by omega⟩ = placement.bank (Fin.castLE (by decide) i))
    (S F : Stacks T A) (hbank : embStk placement.bank F = embStk placement.bank S) :
    releaseReplicaCouplingNativeCost (embStk e F) = releaseReplicaCouplingNativeCost (embStk e S) := by
  apply releaseReplicaCouplingNativeCost_eq_of_native_frame
  intro i
  change F.R (e ⟨i.val,by omega⟩) = S.R (e ⟨i.val,by omega⟩)
  rw [hnative i]
  exact congrArg (fun B : Stacks 168 A => B.R (Fin.castLE (by decide) i)) hbank

theorem releaseReplicaCouplingNativeCost_eq_of_caller_frame (S F : Stacks 389 A)
    (hbank : embStk ReplicaCouplingPlacement.standard.bank (embStk (Fin.castLE (by decide : 300 ≤ 389)) F) =
      embStk ReplicaCouplingPlacement.standard.bank (embStk (Fin.castLE (by decide : 300 ≤ 389)) S)) :
    releaseReplicaCouplingNativeCost (embStk (fun i : Fin 248 => replicaRecoveryCallerReg (Fin.castLE (by decide) i)) F) =
      releaseReplicaCouplingNativeCost (embStk (fun i : Fin 248 => replicaRecoveryCallerReg (Fin.castLE (by decide) i)) S) := by
  apply releaseReplicaCouplingNativeCost_eq_of_native_frame
  intro i
  have hi := replicaRecoveryCallerReg_native (Fin.castLE (by decide : 117 ≤ 168) i)
  change F.R (replicaRecoveryCallerReg (Fin.castLE (by decide) i)) =
    S.R (replicaRecoveryCallerReg (Fin.castLE (by decide) i))
  have hi' : replicaRecoveryCallerReg (Fin.castLE (by decide : 117 ≤ 259) i) =
      Fin.castLE (by decide : 300 ≤ 389) (ReplicaCouplingPlacement.standard.bank (Fin.castLE (by decide) i)) := hi
  rw [hi']
  exact congrArg (fun B : Stacks 168 A => B.R (Fin.castLE (by decide) i)) hbank

theorem releaseReplicaCouplingNative_after_frame {T : ℕ} {body' : P → Pr P T Q A U}
    (e : Fin 248 → Fin T) (he : Function.Injective e) (p : Pr P T Q A U)
    (v vi : HS T Q A U) (S J : Stacks T A) (m : ℕ)
    (hex : Exec body' p (mk v S) m (mk vi J))
    (hframe : ∀ i : Fin 117, J.R (e ⟨i.val,by omega⟩) = S.R (e ⟨i.val,by omega⟩)) :
    ∃ v' F, v'.user = vi.user ∧
      Exec body' (.seq p (embProg e Empty.elim (releaseReplicaCouplingNative (P := Empty))))
        (mk v S) (m+releaseReplicaCouplingNativeCost (embStk e S)) (mk v' F) ∧
      embStk e F = releasedReplicaCouplingNative (embStk e J) ∧
      (∀ k, (∀ i, e i ≠ k) → F.L k = J.L k ∧ F.R k = J.R k) := by
  obtain ⟨vf,hu,hrelease⟩ := releaseReplicaCouplingNative_exec (body := fun z : Empty => nomatch z)
    (embDn e vi) (embStk e J)
  obtain ⟨v',hv,hu',hlift⟩ := exec_emb_ovr (body' := body') (ι := Empty.elim)
    he (fun z => nomatch z) hrelease vi rfl J rfl
  have hcost := releaseReplicaCouplingNativeCost_eq_of_native_frame (embStk e S) (embStk e J) hframe
  rw [hcost] at hlift
  exact ⟨v',_,hu'.trans hu,Exec.seq hex hlift,embStk_ovr he _ J,
    fun k hk => embOvr_off _ J hk⟩

theorem ReplicaRecoveryCoreReady.of_coupling_release {s : ℕ} [NeZero s]
    (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 248 A)
    (hbank : PackedPreparedBank H.precision H.wordWidth W
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (embStk packedBoundaryRecoveryBase S))
    (hheaders : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
      H.origin (H.origin+H.span) H.metadataWidth H.wordWidth (embStk packedRecoveryRuntimeReg S))
    (h143 : S.R 143 = [])
    (hprivate : ∀ k : Fin 248, 242 ≤ k.val → S.L k = [] ∧ S.R k = [])
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = [])
    (hrows : (S.R 140).length = 2*H.band+1)
    (hpage : S.R 138 = cstream A H.wordWidth
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span))
    (hcount : (S.R 139).length =
      (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length) :
    ReplicaRecoveryCoreReady H W (releasedReplicaCouplingNative S) := by
  have hhigh := releasedReplicaCouplingNative_high S
  constructor
  · exact releasedReplicaCouplingNative_bank hbank
  · exact (hhigh 143 (by decide)).trans h143
  · intro k hk; exact (hprivate k hk).1
  · intro k hk; exact (hhigh k (by omega)).trans (hprivate k hk).2
  · apply hheaders.masters.of_frame
    intro k hk
    apply hhigh
    simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hhigh 118 (by decide)]; exact hheaders.stage
  · rw [hhigh 120 (by decide)]; exact hheaders.level
  · intro i h93 h110 h116
    exact releasedReplicaCouplingNative_blank S i h93 h110
  · intro k hk
    apply (hhigh k ?_).trans (hclean k hk)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hhigh 140 (by decide)]; exact hrows
  · exact (hhigh 138 (by decide)).trans hpage
  · rw [hhigh 139 (by decide)]; exact hcount
  · have hg := hheaders.geometry
    have heq : (H.origin+H.span)-H.origin = H.span := Nat.add_sub_cancel_left _ _
    rw [heq] at hg
    apply hg.of_frame
    · exact hhigh 163 (by decide)
    · intro k hk
      apply hhigh
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
