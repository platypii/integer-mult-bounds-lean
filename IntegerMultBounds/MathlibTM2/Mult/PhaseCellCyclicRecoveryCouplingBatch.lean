module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingLoop
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! One retained master initializes the paired recovery loop. Count setup is
paid once and the numerical scratch reserve is shared by all replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "jointSource" => CyclicRecoveryPlacement.bank 132
local notation "clock" => CyclicRecoveryPlacement.bank 228
local notation "master" => CyclicRecoveryPlacement.bank 229
local notation "copyTmp" => CyclicRecoveryPlacement.bank 227
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

noncomputable def cyclicRecoveryCouplingBatch (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  .seq (ucopy master clock copyTmp) (cyclicRecoveryCouplingLoop hQ)

theorem cyclicRecoveryCouplingBatch_exec_within (H K : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (rows : List (CyclicRecoveryRow s))
    (hfitsL : ∀ row ∈ rows, ∀ j, Fits H.wordWidth (row.1 j))
    (hfitsR : ∀ row ∈ rows, ∀ j, Fits K.wordWidth (row.1 j))
    (tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))) (v : HS 840 Q A U) (S : Stacks 840 A)
    (headersL : ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather buffersL S)
    (headersR : ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR S)
    (cacheL : CachedRecoveryCouplingReady H rawL pageL (embStk CyclicRecoveryPlacement.leftJob.coupling.bank S))
    (cacheR : CachedRecoveryCouplingReady K rawR pageR (embStk CyclicRecoveryPlacement.rightJob.coupling.bank S))
    (hsource : S.R jointSource = rows.flatMap (fun row => cyclicRecoveryField H row.1++cyclicRecoveryField K row.1)++tail)
    (hrhsL : S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = rows.flatMap (fun row => cyclicRecoveryField H row.2.1)++rhsL)
    (hrhsR : S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = rows.flatMap (fun row => cyclicRecoveryField K row.2.2)++rhsR)
    (hmaster : (S.R master).length = rows.length) (hclock : S.R clock = []) (htmp : S.R copyTmp = []) :
    ∃ vf F m, vf.user = v.user ∧
      m ≤ (4*rows.length+4)+(rows.length*(cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K+3)+2) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*(4*rows.length+4)+(cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
          cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ)))
        depth (cyclicRecoveryCouplingBatch hQ) (mk v S) m (mk vf F)) ∧ F.R clock = [] ∧
      CyclicRecoveryCouplingCursor H K buffersL buffersR rows [] tail rhsL rhsR rawL rawR pageL pageR S F := by
  have hstart : CyclicRecoveryCouplingCursor H K buffersL buffersR [] rows
      tail rhsL rhsR rawL rawR pageL pageR S S := by
    refine ⟨hsource,hrhsL,hrhsR,?_,?_,?_,?_,headersL,headersR,?_,?_,rfl,rfl,rfl,?_⟩
    · simp
    · simp
    · simp
    · simp
    · simpa using cacheL
    · simpa using cacheR
    · intro k _; rfl
  obtain ⟨vi,hu₁,he₁⟩ := ucopy_exec (body := body)
    (CyclicRecoveryPlacement.bank_injective.ne (by decide : (229 : Fin 240) ≠ 228))
    (CyclicRecoveryPlacement.bank_injective.ne (by decide : (229 : Fin 240) ≠ 227))
    (CyclicRecoveryPlacement.bank_injective.ne (by decide : (228 : Fin 240) ≠ 227)) v S htmp
  let J : Stacks 840 A := {S with R := Function.update S.R clock (List.replicate rows.length tick)}
  have he₁' : Exec body (ucopy master clock copyTmp) (mk v S) (4*rows.length+4) (mk vi J) := by
    simpa only [J,hmaster,hclock,List.append_nil] using he₁
  have hJ := hstart.update_clock (List.replicate rows.length tick)
  obtain ⟨vf,F,m,hu₂,hm,he₂,hclockF,hcursor⟩ := cyclicRecoveryCouplingLoop_exec_within (body := body)
    H K hQ hA hsepL hsepR buffersL buffersR rows hfitsL hfitsR tail rhsL rhsR rawL rawR pageL pageR vi J
    hJ.headersL hJ.headersR (by simpa using hJ.cacheL) (by simpa using hJ.cacheR)
    hJ.source hJ.rhsL hJ.rhsR (by simp [J])
  refine ⟨vf,F,(4*rows.length+4)+m,hu₂.trans hu₁,Nat.add_le_add_left hm _,?_,hclockF,?_⟩
  · intro depth
    have hnative : mnNativePushBound 2 (ucopy (P := P) (Q := Q) (A := A) (U := U) master clock copyTmp) := by
      simp [ucopy,umulSym,scanR,drainR,keepIn,pushN,moveR,moveStep,whileR,popDo,peekR,mnNativePushBound,mnActPush]
    have hc := mn_native_exec_within he₁' 2 hnative depth
      (mnSize (mk v S)+depth+2*(4*rows.length+4)) (by omega)
    exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ hc (he₂ depth)
  · exact CyclicRecoveryCouplingCursor.base_clock (List.replicate rows.length tick) hcursor

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
