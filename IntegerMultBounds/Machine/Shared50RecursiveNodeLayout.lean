import IntegerMultBounds.Machine.RecursiveRowsNode
import IntegerMultBounds.Machine.Shared50RecursiveSegments
import IntegerMultBounds.Networks.Shared50FixedControl

/-! Actual World enumeration for recursive nodes. World wires retain their
existing numeric slots; the common input/output occupies a separate final slot. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
noncomputable section
open Networks
open Shared50GlobalBudget (World)
open Shared50TapeGlobal (roleCount roleEquiv)
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)

theorem roleCount_eq_W : roleCount = Shared50Parameters.W :=
  Shared50GlobalBudget.world_card.symm.trans Shared50GlobalBudget.world_card_eq_W

def common : Fin (roleCount+1) := Fin.last roleCount
def world (i : World) : Fin (roleCount+1) := Fin.castAdd 1 (roleEquiv.symm i)

def wires : Fin (1+roleCount) → Fin (roleCount+1) :=
  Fin.addCases (fun _ => common) (Fin.castAdd 1)

theorem wires_common : wires (Fin.castAdd roleCount (0 : Fin 1)) = common := rfl
@[simp] theorem wires_role (i : Fin roleCount) : wires (Fin.natAdd 1 i) = Fin.castAdd 1 i := by
  simp only [wires,Fin.addCases_right]

theorem world_ne_common (i : World) : world i ≠ common := by
  intro he
  have hh := congrArg Fin.val he
  have hi := (roleEquiv.symm i).isLt
  change (roleEquiv.symm i).val = roleCount at hh
  omega

theorem wires_injective : Function.Injective wires := by
  intro i j he
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => congr 1; exact Subsingleton.elim _ _
    | right j =>
      simp only [wires,Fin.addCases_left,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change roleCount = j.val at hh
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [wires,Fin.addCases_left,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change i.val = roleCount at hh
      omega
    | right j =>
      simp only [wires,Fin.addCases_right] at he
      exact congrArg (Fin.natAdd 1) (Fin.castAdd_injective _ _ he)

/-- Same role number used by every original nonrecursive segment. -/
theorem segment_wire (seg : Shared50OrderedPieces.Segment) :
    world seg.wire = Fin.castAdd 1 (Shared50RecursiveSegments.wire seg) := rfl

def routeEquiv : Equiv.Perm World :=
  ⟨Shared50ShearEndpoints.route,Shared50ShearEndpoints.route,
    Shared50ShearEndpoints.route_involutive,Shared50ShearEndpoints.route_involutive⟩

/-- Physical merge source permutation, conjugated through the existing enumeration. -/
def mergeRoute : Equiv.Perm (Fin roleCount) :=
  roleEquiv.trans (routeEquiv.trans roleEquiv.symm)

@[simp] theorem mergeRoute_apply (i : Fin roleCount) :
    mergeRoute i = roleEquiv.symm (Shared50ShearEndpoints.route (roleEquiv i)) := rfl
@[simp] theorem mergeRoute_symm (i : Fin roleCount) :
    mergeRoute.symm i = roleEquiv.symm (Shared50ShearEndpoints.route (roleEquiv i)) := rfl

theorem mergeRoute_involutive : Function.Involutive mergeRoute := by
  intro i
  simp only [mergeRoute_apply,Equiv.apply_symm_apply]
  rw [Shared50ShearEndpoints.route_involutive,Equiv.symm_apply_apply]

def entry {u : ℕ} := RecursiveRowsNode.entry (u := u) wires wires_injective
def exit {u : ℕ} := RecursiveRowsNode.exit (u := u) mergeRoute wires wires_injective

end
end IntegerMultBounds.Machine.Shared50RecursiveNodeLayout
