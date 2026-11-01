module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeReplicaBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBoundaryPhasePlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryReady

/-! Shared boundary setup runs once in the displaced phase bank. Its complete
post-state agrees with the initial state on the native recovery bank, so it
preserves generated factors and all recovery readiness without reconstruction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

def retainedReplicaBoundarySetup : Pr P 255 Q A U :=
  embProg replicaBoundaryPhaseReg Empty.elim (initializeReplicaBoundaryRhs (P := Empty))

def retainedReplicaBoundarySetupState (H : ReplicaHaloProblem s) (S : Stacks 255 A) : Stacks 255 A :=
  embOvr replicaBoundaryPhaseReg (initializedReplicaBoundaryRhsState H (embStk replicaBoundaryPhaseReg S)).get S

theorem retainedReplicaBoundarySetupState_native (H : ReplicaHaloProblem s) (S : Stacks 255 A) :
    embStk (Fin.castLE (by decide : 248 ≤ 255)) (retainedReplicaBoundarySetupState H S) =
      embStk (Fin.castLE (by decide : 248 ≤ 255)) S := by
  let B := initializedReplicaBoundaryRhsState H (embStk replicaBoundaryPhaseReg S)
  have hL : (retainedReplicaBoundarySetupState H S).L = S.L := embOvr_left_of_eq S B rfl
  refine Stacks.ext ?_ ?_ (congrArg (fun L => L ∘ Fin.castLE (by decide : 248 ≤ 255)) hL) ?_
  · change B.inp = S.inp
    rfl
  · change B.out = S.out
    rfl
  · funext k
    classical
    by_cases himage : ∃ i, replicaBoundaryPhaseReg i = Fin.castLE (by decide : 248 ≤ 255) k
    · obtain ⟨i,hi⟩ := himage
      have hh := embOvr_get replicaBoundaryPhaseReg_injective B.get S (.rt i)
      change (retainedReplicaBoundarySetupState H S).R (replicaBoundaryPhaseReg i) = (B.R i).map id at hh
      have hnot : i ∉ [116,117,118,120,124,167] := by
        intro hm
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals have hv := congrArg (fun k : Fin 255 => k.val) hi
        all_goals simp only [replicaBoundaryPhaseReg_count,replicaBoundaryPhaseReg_floor,
          replicaBoundaryPhaseReg_parity,replicaBoundaryPhaseReg_bytes,replicaBoundaryPhaseReg_rhsVolume,
          replicaBoundaryPhaseReg_mask,Fin.val_natCast,Fin.coe_castLE] at hv
        all_goals have hb := k.isLt; norm_num at hv; omega
      have hB := initializedReplicaBoundaryRhsState_frame H (embStk replicaBoundaryPhaseReg S) i hnot
      change (retainedReplicaBoundarySetupState H S).R (Fin.castLE (by decide) k) = S.R (Fin.castLE (by decide) k)
      rw [←hi]
      exact (hh.trans (List.map_id _)).trans hB
    · have hoff : ∀ i, replicaBoundaryPhaseReg i ≠ Fin.castLE (by decide : 248 ≤ 255) k := by
        intro i hi; exact himage ⟨i,hi⟩
      exact (embOvr_off B.get S hoff).2

theorem retainedReplicaBoundarySetup_exec (H : ReplicaHaloProblem s) (hA : 4 ≤ A)
    (v : HS 255 Q A U) (S : Stacks 255 A) :
    let J := embStk replicaBoundaryPhaseReg S
    CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) J) →
    (J.R 123).length = H.span*H.wordWidth → (J.R 130).length = H.wordWidth →
    (∀ k : Fin 242, k.val < 77 → J.R k = []) →
    (∀ k ∈ [(104 : Fin 242),105,116,117,118,120,124,143,167], J.R k = []) →
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeReplicaBoundaryRhsCost H ∧
      Exec body retainedReplicaBoundarySetup (mk v S) n (mk v' (retainedReplicaBoundarySetupState H S)) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (retainedReplicaBoundarySetupState H S)) ∧
      embStk (Fin.castLE (by decide : 248 ≤ 255)) (retainedReplicaBoundarySetupState H S) =
        embStk (Fin.castLE (by decide : 248 ≤ 255)) S := by
  dsimp only
  intro hmeta hvolume hwidth hscratch hfresh
  obtain ⟨vi,n,hu,hn,he,hready⟩ := initializeReplicaBoundaryRhs_exec (body := fun z : Empty => nomatch z)
    H hA (embDn replicaBoundaryPhaseReg v) (embStk replicaBoundaryPhaseReg S)
    hmeta hvolume hwidth hscratch hfresh
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaBoundaryPhaseReg_injective (fun z => nomatch z) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,he',?_,retainedReplicaBoundarySetupState_native H S⟩
  change ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg
    (embOvr replicaBoundaryPhaseReg (initializedReplicaBoundaryRhsState H (embStk replicaBoundaryPhaseReg S)).get S))
  rw [embStk_ovr replicaBoundaryPhaseReg_injective]
  exact hready

theorem retainedReplicaBoundarySetup_of_core_exec (H : ReplicaHaloProblem s) (W : ℕ) (hA : 4 ≤ A)
    (v : HS 255 Q A U) (S : Stacks 255 A)
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S))
    (hvolume : (S.R 251).length = H.span*H.wordWidth)
    (hblank : ∀ k ∈ ([248,249,250,252,253,254] : List (Fin 255)), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeReplicaBoundaryRhsCost H ∧
      Exec body retainedReplicaBoundarySetup (mk v S) n (mk v' (retainedReplicaBoundarySetupState H S)) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (retainedReplicaBoundarySetupState H S)) ∧
      ReplicaRecoveryCoreReady H W
        (embStk (Fin.castLE (by decide : 248 ≤ 255)) (retainedReplicaBoundarySetupState H S)) := by
  have hfixed (i : Fin 242) (hi : i ∉ [116,117,118,120,123,124,167]) :
      (embStk replicaBoundaryPhaseReg S).R i = S.R (Fin.castLE (by decide) i) := by
    change S.R (replicaBoundaryPhaseReg i) = _
    rw [replicaBoundaryPhaseReg_fixed i hi]
  have hmeta : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) (embStk replicaBoundaryPhaseReg S)) := by
    apply hcore.geometry.of_frame
    · exact hfixed 163 (by decide)
    · intro k hk
      apply hfixed
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,Fin.castLE] at hk ⊢
      norm_num at hk ⊢
      omega
  have hnative (i : Fin 242) (hi : i.val < 117) (h93 : i.val ≠ 93) (h110 : i.val ≠ 110)
      (h116 : i.val ≠ 116) : S.R (Fin.castLE (by decide) i) = [] :=
    hcore.native ⟨i.val,hi⟩ (by intro h; exact h93 (congrArg Fin.val h))
      (by intro h; exact h110 (congrArg Fin.val h)) (by intro h; exact h116 (congrArg Fin.val h))
  obtain ⟨v',n,hu,hn,he,hphysical,hview⟩ := retainedReplicaBoundarySetup_exec (body := body) H hA v S
    hmeta (by change (S.R (replicaBoundaryPhaseReg 123)).length = _; simpa using hvolume)
    (by rw [hfixed 130 (by decide)]; exact hcore.masters.width)
    (by
      intro k hk
      rw [hfixed k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
        norm_num
        omega)]
      exact hnative k (by omega) (by omega) (by omega) (by omega))
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hfixed 104 (by decide)]; exact hnative 104 (by decide) (by decide) (by decide) (by decide)
      · rw [hfixed 105 (by decide)]; exact hnative 105 (by decide) (by decide) (by decide) (by decide)
      · exact hblank 253 (by decide)
      · exact hblank 248 (by decide)
      · exact hblank 249 (by decide)
      · exact hblank 250 (by decide)
      · exact hblank 252 (by decide)
      · rw [hfixed 143 (by decide)]; exact hcore.rhs
      · exact hblank 254 (by decide))
  exact ⟨v',n,hu,hn,he,hphysical,by rw [hview]; exact hcore⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
