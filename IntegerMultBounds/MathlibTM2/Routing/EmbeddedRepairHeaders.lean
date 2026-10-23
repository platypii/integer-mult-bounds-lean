module

public import IntegerMultBounds.MathlibTM2.Routing.RepairSharedHeaderLayout

/-! The existing header generator works over any injectively embedded repair
core. Its workspace and program do not depend on a particular descriptor engine. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

variable {N : ℕ}

def embeddedRepairHeaderCore (e : Fin repairT → Fin N) (r : HeaderCoreRole) : Fin N :=
  e (repairRoutingConfig (repairHeaderCoreKey r))

theorem embeddedRepairHeaderCore_injective (e : Fin repairT → Fin N) (he : Function.Injective e) :
    Function.Injective (embeddedRepairHeaderCore e) := by
  intro r s hr
  have hh := he hr
  cases r <;> cases s <;> simp_all [repairHeaderCoreKey, repairRoutingConfig, placedSelectiveConfig, repairRoutingRole]

def embeddedRepairHeaderBank (e : Fin repairT → Fin N) (c : Fin 2) : RepairHeaderReg → Fin (sharedHeaderT N) :=
  sharedHeaderBank (embeddedRepairHeaderCore e) c

def embeddedRepairHeaderRaw (e : Fin repairT → Fin N) (i : Fin repairT) : Fin (sharedHeaderT N) := sharedHeaderCore (e i)

theorem embeddedRepairHeaderRaw_injective (e : Fin repairT → Fin N) (he : Function.Injective e) :
    Function.Injective (embeddedRepairHeaderRaw e) := sharedHeaderCore_injective.comp he

theorem embeddedRepairHeaderBank_injective (e : Fin repairT → Fin N) (he : Function.Injective e) (c : Fin 2) :
    Function.Injective (embeddedRepairHeaderBank e c) :=
  sharedHeaderBank_injective _ (embeddedRepairHeaderCore_injective e he) c

theorem embeddedRepairHeaderBank_cross (e : Fin repairT → Fin N) (he : Function.Injective e)
    (r : RepairHeaderReg) (i : Fin 5) :
    embeddedRepairHeaderBank e 1 r ≠ embeddedRepairHeaderBank e 0 (.exchange (.base (.header i))) :=
  sharedHeaderBank_cross _ (embeddedRepairHeaderCore_injective e he) r i

theorem embeddedRepairHeaderBinary_separate (e : Fin repairT → Fin N) (he : Function.Injective e)
    (c : Fin 2) (i : Fin 2) (r : RepairHeaderReg) : sharedHeaderBinary i ≠ embeddedRepairHeaderBank e c r :=
  sharedHeaderBinary_separate _ (embeddedRepairHeaderCore_injective e he) c i r

@[simp] theorem embeddedRepairHeaderBank_header (e : Fin repairT → Fin N) (c : Fin 2) (i : Fin 5) :
    embeddedRepairHeaderBank e c (.exchange (.base (.header i))) = embeddedRepairHeaderRaw e (repairRoutingConfig (.header c i)) := rfl

@[simp] theorem embeddedRepairHeaderBank_dimension (e : Fin repairT → Fin N) (c : Fin 2) (i : Fin 5) :
    embeddedRepairHeaderBank e c (.dimension i) = embeddedRepairHeaderRaw e (repairRoutingConfig (.field i)) := rfl

@[simp] theorem embeddedRepairHeaderBank_block (e : Fin repairT → Fin N) (c : Fin 2) :
    embeddedRepairHeaderBank e c (.exchange (.base .block)) = embeddedRepairHeaderRaw e (repairRoutingConfig .block) := rfl

theorem embeddedRepairHeaders_exec {Q A : ℕ} {P U : Type}
    (e : Fin repairT → Fin N) (he : Function.Injective e)
    (body : P → Pr P (sharedHeaderT N) Q A U) (p : Par) (X rb R B L Lr Lw : ℕ)
    (hR : R < 2 ^ Lr) (hR0 : 0 < R) (hw : p.wc < 2 ^ Lw)
    (hB : fieldsLen (selectiveKeyLen p X rb) + B < 2 ^ L)
    (hB0 : 0 < fieldsLen (selectiveKeyLen p X rb) + B)
    (v : HS (sharedHeaderT N) Q A U) (S : Stacks (sharedHeaderT N) A)
    (hdim : ∀ f, (S.R (embeddedRepairHeaderRaw e (repairRoutingConfig (.field f)))).length = selectiveLen p X f)
    (hrowInput : S.R (sharedHeaderBinary 0) = binSyms Lr R)
    (hwidthInput : S.R (sharedHeaderBinary 1) = binSyms Lw p.wc)
    (hblock : S.R (embeddedRepairHeaderRaw e (repairRoutingConfig .block)) = binSyms L (fieldsLen (selectiveKeyLen p X rb) + B))
    (hheaders : ∀ c i, S.R (embeddedRepairHeaderBank e c (.exchange (.base (.header i)))) = [])
    (hwork : ∀ r : HeaderWorkRole, (∀ i, r ≠ .binary i) → S.R (sharedHeaderWork r) = []) :
    ∃ (v' : HS (sharedHeaderT N) Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ 2 * (14 * (p.wc + p.wy + X) + 18 * Lr + 24 * Lw + 52 * L + 280) ∧
      Exec body (binaryRepairHeaderPairProgram sharedHeaderBinary (embeddedRepairHeaderBank e)) (mk v S) steps
        (mk v' { S with R := repairHeaderPairBank p X rb R B (embeddedRepairHeaderBank e) S.R }) := by
  apply binaryRepairHeaderPair_exec body sharedHeaderBinary (embeddedRepairHeaderBank e)
    (embeddedRepairHeaderBank_injective e he) (embeddedRepairHeaderBinary_separate e he) (embeddedRepairHeaderBank_cross e he)
    p X rb R B L Lr Lw hR hR0 hw hB hB0 v S
  · intro c f; simpa only [embeddedRepairHeaderBank_dimension] using hdim f
  · exact hrowInput
  · exact hwidthInput
  · intro c; simpa only [embeddedRepairHeaderBank_block] using hblock
  · intro c r hr
    cases r with
    | lowerExp => exact hwork .lower (by intro i; simp)
    | triple => exact hwork .triple (by intro i; simp)
    | base r =>
      cases r with
      | block => exact (hr rfl).elim
      | header i => exact hheaders c i
      | rowExp => exact hwork .rowExp (by intro i; simp)
      | gapExp => exact hwork .gapExp (by intro i; simp)
      | target => exact hwork .target (by intro i; simp)
      | rows => exact hwork .rows (by intro i; simp)
      | scratch i => exact hwork (.scratch i) (by intro j; simp)

end
end IntegerMultBounds.MathlibTM2.Routing
