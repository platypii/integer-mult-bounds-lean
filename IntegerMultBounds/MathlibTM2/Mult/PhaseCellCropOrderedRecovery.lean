module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedOrderedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryOrderPlacement

/-! Ordered local recovery uses the existing crop bank with no fresh scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace ComputedRecoveryPlan
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem crop_ordered_exec (plan : ComputedRecoveryPlan T) (b : RawRecoveryProgramBounds Q A U)
    (normalize : RecoveryNormalizePlan T) (queue : RecoveryParameterQueue normalize)
    (crop : RecoveryCropPlacement plan) (link : RecoveryCropNormalizeLink normalize queue)
    (hreg : link.reg = crop.reg)
    (hsupportMaster : ∀ k, normalize.support queue k → ∀ i, plan.master.masters i ≠ k)
    (hsupportPayload : ∀ k, normalize.support queue k → k ≠ plan.work 124)
    (hreplicaCount : plan.replicas ≠ plan.count) (hreplicaSpare : plan.replicas ≠ plan.spare)
    (r : PackedNormalizedJob A s) (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore)
    (v : HS T Q A U) (S : Stacks T A)
    (hready : normalize.UnaryReady queue r r.Fs.length wl S)
    (hp : (S.R plan.precision).length = r.p) (hW : (S.R plan.packet).length = r.W)
    (hN : (S.R plan.replicas).length = r.Fs.length)
    (hvalues : ∀ i, (S.R (plan.master.parameters i)).length = r.masterInput.values i)
    (hwidth : S.R (plan.master.scalar .wr) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (plan.master.scalar i) = [])
    (hmasters : ∀ i, S.R (plan.master.masters i) = [])
    (hmasterScratch : ∀ k ∈ [plan.master.word,plan.master.saved,plan.master.tmp,plan.master.queue], S.R k = [])
    (hblank : ∀ i, i ≠ 124 → S.R (plan.work i) = []) (hleft : ∀ i, S.L (plan.work i) = [])
    (hpayload : S.R (plan.work 124) = cstream A r.W (r.Fs.map (packedInterval r.a (r.b-r.a))).flatten)
    (hscratch : ∀ k ∈ [plan.count,plan.tmp,plan.spare], S.R k = [])
    (hclock : S.R plan.clock = []) (hsaved : S.R plan.saved = []) (hsavedClock : S.R plan.savedClock = [])
    (hoffset : (S.R (crop.reg 3)).length = r.radius)
    (hrows : (S.R (crop.reg 4)).length = coreLength s r.coreWidth r.k)
    (hpacketRows : plan.packet ≠ crop.reg 4) (hpacketReplicas : plan.packet ≠ plan.replicas)
    (hpacketDestination : plan.packet ≠ crop.reg 12) :
    ∃ word v' n, r.output word ∧ v'.user = v.user ∧
      n ≤ plan.normalizedTimeCost b r+restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W ∧
      Exec body (.seq (plan.normalizedProgram b normalize queue link)
        (embProg crop.orderPlacement Empty.elim restoreReplicaOrder)) (Host.mk v S) n
        (Host.mk v' (orderedFinal plan normalize crop.orderPlacement S word)) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule plan.src plan.saved plan.tmp plan.clock plan.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            plan.work plan.src plan.saved plan.count plan.tmp plan.spare plan.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (plan.normalizedStock b r Cprog+2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))
          depth (.seq (plan.normalizedProgram b normalize queue link) (embProg crop.orderPlacement Empty.elim restoreReplicaOrder))
          (Host.mk v S) n (Host.mk v' (orderedFinal plan normalize crop.orderPlacement S word)) := by
  have hports := crop.orderPlacement_ports
  have hsource : crop.orderPlacement 6 = normalize.src := by
    rw [hports.2.2.2.1]
    exact ((congrFun hreg 12).symm.trans link.source.symm)
  exact plan.ordered_exec b normalize queue crop link hreg hsupportMaster hsupportPayload
    hreplicaCount hreplicaSpare r wl hwl v S hready hp hW hN hvalues hwidth hscalar hmasters
    hmasterScratch hblank hleft hpayload hscratch hclock hsaved hsavedClock hoffset hrows
    crop.orderPlacement (crop.orderPlacement_injective hpacketRows hpacketReplicas hpacketDestination)
    hsource crop.orderPlacement_outside hrows hW
    (by rw [crop.orderPlacement_ports.2.2.1]; exact hN)
    (fun k hk => Or.inl (crop.orderPlacement_scratch k hk))

end ComputedRecoveryPlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
