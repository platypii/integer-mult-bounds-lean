module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingRowReads
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingRowStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! The checked paired worker advances the chronological cursor and preserves
endpoint stock. Its scratch reserve is independent of completed replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "jointSource" => CyclicRecoveryPlacement.bank 132
local notation "clock" => CyclicRecoveryPlacement.bank 228
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

theorem cyclicRecoveryCouplingStep_exec_within (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (done todo : List (CyclicRecoveryRow s)) (row : CyclicRecoveryRow s)
    (hfitsL : ∀ j, Fits H.wordWidth (row.1 j)) (hfitsR : ∀ j, Fits K.wordWidth (row.1 j))
    (tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))) (S F : Stacks 840 A) (v : HS 840 Q A U)
    (cursor : CyclicRecoveryCouplingCursor H K buffersL buffersR done (row::todo)
      tail rhsL rhsR rawL rawR pageL pageR S F) :
    ∃ vf G m, vf.user = v.user ∧ m ≤ cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        (cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
          cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ))
        depth (cyclicRecoveryCouplingRow hQ) (mk v F) m (mk vf G)) ∧
      G.R clock = F.R clock ∧
      CyclicRecoveryCouplingCursor H K buffersL buffersR (done++[row]) todo
        tail rhsL rhsR rawL rawR pageL pageR S G ∧
      mnSize (mk vf G) ≤ mnSize (mk v F) := by
  let rest := todo.flatMap (fun row => cyclicRecoveryField H row.1++cyclicRecoveryField K row.1)++tail
  let rhsRestL := todo.flatMap (fun row => cyclicRecoveryField H row.2.1)++rhsL
  let rhsRestR := todo.flatMap (fun row => cyclicRecoveryField K row.2.2)++rhsR
  have hsource : F.R jointSource = cyclicRecoveryField H row.1++(cyclicRecoveryField K row.1++rest) := by
    simpa [rest,List.append_assoc] using cursor.source
  have hL : F.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = cyclicRecoveryField H row.2.1++rhsRestL := by
    simpa [rhsRestL,List.append_assoc] using cursor.rhsL
  have hR : F.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = cyclicRecoveryField K row.2.2++rhsRestR := by
    simpa [rhsRestR,List.append_assoc] using cursor.rhsR
  have run := fun depth => cyclicRecoveryCouplingRow_exec_within (body := body) H K hQ hA hsepL hsepR
    buffersL buffersR row.1 row.1 row.2.1 row.2.2 hfitsL hfitsR rest rhsRestL rhsRestR
    (done.reverse.flatMap (cyclicRecoveryOutputL H)++rawL) (done.reverse.flatMap (cyclicRecoveryOutputR K)++rawR)
    pageL pageR v F cursor.headersL cursor.headersR cursor.cacheL cursor.cacheR hsource hL hR depth
  obtain ⟨vf,m,hu,hm,he,hhL,hhR,hcL,hcR⟩ := run 0
  let G := cyclicRecoveryCouplingRowState H K row.1 row.1 rest rhsRestL rhsRestR
    (cyclicRecoveryOutputL H row) (cyclicRecoveryOutputR K row) F
  have hreads := cyclicRecoveryCouplingRowState_reads H K row.1 row.1 rest rhsRestL rhsRestR
    (cyclicRecoveryOutputL H row) (cyclicRecoveryOutputR K row) F
  obtain ⟨hsrcG,hLG,hRG,houtLG,houtRG,harchLG,harchRG⟩ := hreads
  have hframe (k : Fin 840) (hs : k ≠ jointSource)
      (hL93 : k ≠ CyclicRecoveryPlacement.leftJob.coupling.bank 93)
      (hL110 : k ≠ CyclicRecoveryPlacement.leftJob.coupling.bank 110)
      (hL125 : k ≠ CyclicRecoveryPlacement.leftJob.plan.gather 125)
      (hR93 : k ≠ CyclicRecoveryPlacement.rightJob.coupling.bank 93)
      (hR110 : k ≠ CyclicRecoveryPlacement.rightJob.coupling.bank 110)
      (hR125 : k ≠ CyclicRecoveryPlacement.rightJob.plan.gather 125) : G.R k = F.R k :=
    cyclicRecoveryCouplingRowState_frame H K row.1 row.1 rest rhsRestL rhsRestR _ _ F k hs hL93 hL110 hL125 hR93 hR110 hR125
  refine ⟨vf,G,m,hu,hm,?_,?_,?_,?_⟩
  · intro depth
    obtain ⟨vf',m',_,_,he',_⟩ := run depth
    obtain ⟨ht,hz⟩ := he'.toExec.unique he.toExec
    exact he'.cast ht hz
  · exact hframe clock (CyclicRecoveryPlacement.bank_injective.ne (by decide : (228 : Fin 240) ≠ 132))
      (CyclicRecoveryPlacement.native_left_disjoint 228 _ (.bank 93)).symm
      (CyclicRecoveryPlacement.native_left_disjoint 228 _ (.bank 110)).symm
      (CyclicRecoveryPlacement.native_left_disjoint 228 _ (.gather 125)).symm
      (CyclicRecoveryPlacement.native_right_disjoint 228 _ (.bank 93)).symm
      (CyclicRecoveryPlacement.native_right_disjoint 228 _ (.bank 110)).symm
      (CyclicRecoveryPlacement.native_right_disjoint 228 _ (.gather 125)).symm
  · refine ⟨hsrcG,hLG,hRG,?_,?_,?_,?_,hhL,hhR,?_,?_,cursor.input,cursor.output,cursor.left,?_⟩
    · rw [houtLG,cursor.outputL]
      simp [List.reverse_append,List.append_assoc]
    · rw [houtRG,cursor.outputR]
      simp [List.reverse_append,List.append_assoc]
    · rw [harchLG,cursor.archiveL]
      simp [cyclicRecoveryField,List.reverse_append,List.append_assoc]
    · rw [harchRG,cursor.archiveR]
      simp [cyclicRecoveryField,List.reverse_append,List.append_assoc]
    · simpa [G,cyclicRecoveryOutputL,cyclicRecoveryOutputR,cyclicRecoveryField,List.reverse_append,List.append_assoc] using hcL
    · simpa [G,cyclicRecoveryOutputL,cyclicRecoveryOutputR,cyclicRecoveryField,List.reverse_append,List.append_assoc] using hcR
    · intro k hk
      have hoff (i : Fin 840) (hi : i ∈ cyclicRecoveryCouplingPorts) : k ≠ i := by
        intro hi'; apply hk; rw [hi']; exact hi
      rw [hframe k (hoff _ (by simp [cyclicRecoveryCouplingPorts]))
        (hoff _ (by simp [cyclicRecoveryCouplingPorts])) (hoff _ (by simp [cyclicRecoveryCouplingPorts]))
        (hoff _ (by simp [cyclicRecoveryCouplingPorts])) (hoff _ (by simp [cyclicRecoveryCouplingPorts]))
        (hoff _ (by simp [cyclicRecoveryCouplingPorts])) (hoff _ (by simp [cyclicRecoveryCouplingPorts]))]
      exact cursor.frame k hk
  · apply le_of_eq
    exact cyclicRecoveryCouplingRowState_stock H K row.1 row.1 row.2.1 row.2.2 rest rhsRestL rhsRestR _ _
      (by simp [cyclicRecoveryOutputL,cyclicRecoveryField,length_cstream,packedInterval_length _ H.span_fit])
      (by simp [cyclicRecoveryOutputR,cyclicRecoveryField,length_cstream,packedInterval_length _ K.span_fit])
      v vf F hsource hL hR

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
