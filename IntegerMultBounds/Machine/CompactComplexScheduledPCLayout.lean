import IntegerMultBounds.Machine.CompactComplexCompletedLiveLower
import IntegerMultBounds.Machine.CompactComplexCallerWorkingExtraFlow
import Mathlib.Data.List.Nodup

/-! Original saved call PCs and fixed local event entries. All table indices
are chosen from the actual finite schedule, independently of runtime depth. -/
namespace IntegerMultBounds.Machine.CompactComplexScheduledPCLayout
noncomputable section
open Networks
open CompactComplexCompletedLiveLower
open CompactComplexScalarIntegerRows (GroupIndex)
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.calls
  ComplexRecursiveCallSchema.sites schedule groups

/-- Generic original site-major call enumeration contains no duplicate call. -/
theorem callsFor_nodup (es : List ComplexPhaseRowSchedule.Edge) :
    (ComplexRecursiveCallSchema.callsFor es).Nodup := by
  unfold ComplexRecursiveCallSchema.callsFor
  apply List.nodup_flatten.mpr
  constructor
  · intro cs hcs
    obtain ⟨site,rfl⟩ := List.mem_ofFn.mp hcs
    unfold ComplexRecursiveCallSchema.callsAtFor
    apply List.nodup_ofFn_ofInjective
    intro i j he
    apply Fin.ext
    exact congrArg (fun c => c.coordinate.val) he
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    apply List.disjoint_left.mpr
    intro call hi hj
    have hsi : call.site=i := by
      obtain ⟨c,hc⟩ := List.mem_ofFn.mp hi
      rw [←hc]
    have hsj : call.site=j := by
      obtain ⟨c,hc⟩ := List.mem_ofFn.mp hj
      rw [←hc]
    exact (ne_of_lt hij) (hsi.symm.trans hsj)

theorem actual_calls_nodup : ComplexRecursiveCallSchema.calls.Nodup := by
  unfold ComplexRecursiveCallSchema.calls
  exact callsFor_nodup ComplexRecursiveCallSchema.sites

theorem schedule_children_nodup : (childNames schedule).Nodup :=
  schedule_calls.symm ▸ actual_calls_nodup

def scalarGroups : List Event → List GroupIndex
  | [] => []
  | .scalar g::es => g::scalarGroups es
  | .child _::es => scalarGroups es

private theorem scalar_mem (g : GroupIndex) (es : List Event) :
    g∈scalarGroups es ↔ Event.scalar g∈es := by
  induction es with
  | nil => simp [scalarGroups]
  | cons e es ih => cases e <;> simp [scalarGroups,ih]

private theorem child_mem (c : ComplexRecursiveCallSchema.Call) (es : List Event) :
    c∈childNames es ↔ Event.child c∈es := by
  induction es with
  | nil => simp [childNames]
  | cons e es ih => cases e <;> simp [childNames,ih]

private theorem names_nodup (es : List Event)
    (hs : (scalarGroups es).Nodup) (hc : (childNames es).Nodup) : es.Nodup := by
  induction es with
  | nil => exact List.nodup_nil
  | cons e es ih =>
    cases e with
    | scalar g =>
      obtain ⟨hne,ht⟩ := List.nodup_cons.mp hs
      exact List.nodup_cons.mpr ⟨fun h => hne ((scalar_mem g es).mpr h),ih ht hc⟩
    | child c =>
      obtain ⟨hne,ht⟩ := List.nodup_cons.mp hc
      exact List.nodup_cons.mpr ⟨fun h => hne ((child_mem c es).mpr h),ih hs ht⟩

private theorem scalarGroups_append (xs ys : List Event) :
    scalarGroups (xs++ys)=scalarGroups xs++scalarGroups ys := by
  induction xs with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.cons_append,scalarGroups,ih,List.cons_append]

private theorem scalarGroups_children (cs : List ComplexRecursiveCallSchema.Call) :
    scalarGroups (cs.map Event.child)=[] := by
  induction cs with
  | nil => rfl
  | cons c cs ih => exact ih

private theorem assemble_scalarGroups (count : GroupIndex → ℕ) (gs : List GroupIndex)
    (cs : List ComplexRecursiveCallSchema.Call) :
    scalarGroups (assembleWith count gs cs)=gs := by
  induction gs generalizing cs with
  | nil => exact scalarGroups_children cs
  | cons g gs ih =>
    rw [assembleWith,scalarGroups_append,scalarGroups_children]
    exact congrArg (List.cons g) (ih (cs.drop (count g)))

theorem schedule_nodup : schedule.Nodup := by
  apply names_nodup _ _ schedule_children_nodup
  have he : scalarGroups schedule=groups := by
    unfold schedule assemble
    exact assemble_scalarGroups groupCalls groups ComplexRecursiveCallSchema.calls
  rw [he]
  unfold groups
  exact List.nodup_ofFn_ofInjective Function.injective_id

local instance : DecidableEq Event := Classical.typeDecidableEq _

/-- The real child occurs once in the real interleaved schedule. -/
theorem child_event_mem (c : ComplexRecursiveCallSchema.Call) : Event.child c∈schedule :=
  (child_mem c schedule).mp (schedule_calls.symm ▸ ComplexRecursiveCallSchema.calls_complete c)

def callIndex (c : ComplexRecursiveCallSchema.Call) : Fin schedule.length :=
  ⟨schedule.idxOf (.child c),List.idxOf_lt_length_of_mem (child_event_mem c)⟩

theorem callIndex_spec (c : ComplexRecursiveCallSchema.Call) :
    schedule.get (callIndex c)=Event.child c :=
  List.getElem_idxOf (callIndex c).isLt

/-- Any actual occurrence of this child is the same fixed continuation index. -/
theorem callIndex_at (c : ComplexRecursiveCallSchema.Call) (i : Fin schedule.length)
    (hi : schedule.get i=Event.child c) : callIndex c=i :=
  List.nodup_iff_injective_get.mp schedule_nodup ((callIndex_spec c).trans hi.symm)

abbrev originalCount := CompactComplexCallReturn.addresses
abbrev extraCount := 4+schedule.length
abbrev PCs := Fin (originalCount+extraCount+2)

/-- Extra event entries follow the four fixed shared control blocks. -/
def eventPC (i : Fin schedule.length) :=
  GuardedFiniteReturnExtraFlow.extraPC (N:=originalCount) (Fin.natAdd 4 i)

private def finalPCFor (N length : ℕ) : Fin (N+(4+length)+2) :=
  GuardedFiniteReturnExtraFlow.extraPC ⟨3,by omega⟩

private def nextPCFor (N length : ℕ) (i : Fin length) : Fin (N+(4+length)+2) :=
  if h : i.val+1<length then
    GuardedFiniteReturnExtraFlow.extraPC (Fin.natAdd 4 (⟨i.val+1,h⟩ : Fin length))
  else finalPCFor N length

def finalPC := finalPCFor originalCount schedule.length

def nextPC (i : Fin schedule.length) := nextPCFor originalCount schedule.length i

def callNextPC (c : ComplexRecursiveCallSchema.Call) := nextPC (callIndex c)

theorem actual_return_successor (c : ComplexRecursiveCallSchema.Call) (i : Fin schedule.length)
    (hi : schedule.get i=Event.child c) : callNextPC c=nextPC i :=
  congrArg nextPC (callIndex_at c i hi)

theorem eventPC_injective : Function.Injective eventPC := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only [eventPC,GuardedFiniteReturnExtraFlow.extraPC,Fin.val_succ,Fin.val_natAdd] at hv
  omega

/-- A proper event successor is the next literal event entry. -/
theorem nextPC_successor (i : Fin schedule.length) (h : i.val+1<schedule.length) :
    nextPC i=eventPC ⟨i.val+1,h⟩ := by
  unfold nextPC nextPCFor
  rw [dite_eq_left h]
  rfl

/-- The final event goes to the fixed nonleaf return block. -/
theorem nextPC_final (i : Fin schedule.length) (h : ¬i.val+1<schedule.length) :
    nextPC i=finalPC := by
  unfold nextPC nextPCFor finalPC
  rw [dite_eq_right h]


end
end IntegerMultBounds.Machine.CompactComplexScheduledPCLayout
