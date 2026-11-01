module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryBankReady

/-! The shared bank construction instantiates the complete computed ordered
call. All placement and frame-link hypotheses are discharged structurally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
namespace RecoveryBanks
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def orderedProgram (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q A U) : Pr P T Q A U :=
  .seq ((plan bank hinj).normalizedProgram b (normalize bank hinj) (queue bank hinj) (link bank hinj))
    (embProg (crop bank hinj).orderPlacement Empty.elim restoreReplicaOrder)

theorem ordered_exec (bank : RecoveryBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q A U) (r : PackedNormalizedJob A s)
    (wl : List (Fin (A+4))) (hwl : wl.length = r.Bcore) (v : HS T Q A U) (S : Stacks T A)
    (hready : (plan bank hinj).LocalReady (normalize bank hinj) (queue bank hinj) (crop bank hinj) r wl S) :
    let p := plan bank hinj
    let norm := normalize bank hinj
    let c := crop bank hinj
    ∃ word v' n, r.output word ∧ v'.user = v.user ∧
      n ≤ p.normalizedTimeCost b r+restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W ∧
      Exec body (orderedProgram bank hinj b) (Host.mk v S) n
        (Host.mk v' (ComputedRecoveryPlan.orderedFinal p norm c.orderPlacement S word)) ∧
      ∀ Cprog, mnProgPush (descriptorSolverSchedule p.src p.saved p.tmp p.clock p.savedClock
          (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
            p.work p.src p.saved p.count p.tmp p.spare p.result b.hR b.hQ)) ≤ Cprog →
        (∀ f, mnProgPush (body f) ≤ Cprog) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
          (p.normalizedStock b r Cprog+2*restoreReplicaOrderCost r.Fs.length (coreLength s r.coreWidth r.k) r.W))
          depth (orderedProgram bank hinj b) (Host.mk v S) n
          (Host.mk v' (ComputedRecoveryPlan.orderedFinal p norm c.orderPlacement S word)) := by
  dsimp only
  apply ComputedRecoveryPlan.LocalReady.ordered_exec (body := body) (plan bank hinj) b
    (normalize bank hinj) (queue bank hinj) (crop bank hinj) (link bank hinj) rfl
    (normalize_support_masters bank hinj) (normalize_support_payload bank hinj)
    (by simp [plan,hinj.eq_iff]) (by simp [plan,hinj.eq_iff]) r wl hwl v S hready
  · change bank (.control .packet) ≠ bank (.control .cropRows)
    simp [hinj.eq_iff]
  · change bank (.control .packet) ≠ bank (.control .replicas)
    simp [hinj.eq_iff]
  · change bank (.control .packet) ≠ bank (.control .cropDst)
    simp [hinj.eq_iff]

end RecoveryBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
