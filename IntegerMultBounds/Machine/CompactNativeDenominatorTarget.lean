import IntegerMultBounds.Machine.CompactComplexControllerDenominator
import IntegerMultBounds.Machine.CompactComplexDenominatorPolicy

/-! Physical semantic-target construction from retained input-denominator and
child-volume descriptors. Two fixed bodies construct n+volume for a stopped
leaf and n+2*volume for an actual completed network. They retain the originals
and clear their work clock. Choosing the body must use the actual stop branch;
no target word or arithmetic result is supplied to either body. -/
namespace IntegerMultBounds.Machine.CompactNativeDenominatorTarget
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def bank (n volume : ℕ) (t : Option ℕ) : Tapes 4 2 :=
  ⟨![1,1,if t.isSome then 1 else 0,0],
   ![RadixZeroFill.encodedBinary (bits n),RadixZeroFill.encodedBinary (bits volume),
     match t with | none => fun _ => blank | some x => RadixZeroFill.encodedBinary (bits x),fun _ => blank]⟩
def input (n volume : ℕ) := bank n volume none

def copySlots : Fin 2 → Fin 4 := ![0,2]
private theorem copy_injective : Function.Injective copySlots := by decide
def copyProgram := BinaryDescriptorCopyPlaced.program (a:=2) copySlots copy_injective

def addSlots : Fin 3 → Fin 4 := ![2,3,1]
private theorem add_injective : Function.Injective addSlots := by decide
def addPlacement : Fin (3+1) ≃ Fin 4 := InjectivePlacement.placement addSlots add_injective rfl
def addProgram := Placement.placed (BinaryDescriptorAdvance.program (q:=2)) addPlacement

def leafProgram := seq copyProgram addProgram
def networkProgram := seq leafProgram addProgram

def addCost (n volume : ℕ) := 10*volume+2*(bits n).length+7*(bits volume).length+28

def leafCost (n volume : ℕ) := 2*(bits n).length+6+addCost n volume
def networkCost (n volume : ℕ) := leafCost n volume+1+addCost (n+volume) volume

private theorem copied (n volume : ℕ) :
    setTape (input n volume) (2:Fin 4) (RadixZeroFill.encodedBinary (bits n)) 1=bank n volume (some n) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem copy_runs (n volume : ℕ) :
    HoareTime copyProgram (fun v => v=input n volume) (fun v => v=bank n volume (some n))
      (2*(bits n).length+5) := by
  have h := BinaryDescriptorCopyPlaced.copies (input n volume) copySlots copy_injective (bits n) (by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl)
  simp only [copySlots,Matrix.cons_val_one,Matrix.cons_val_zero] at h
  rw [copied] at h
  exact h

private theorem active (n volume t : ℕ) :
    Placement.active addPlacement (bank n volume (some t))=
      BinaryDescriptorAdvance.input (q:=2) (bits t) (bits volume) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [addPlacement,InjectivePlacement.active_slot,addSlots]
  all_goals fin_cases i
  all_goals first | rfl |
    exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm |
    exact CompactGadgetReservationHeadersCore.encoded_binary _

/-- Add the original binary child-volume word into the target while retaining
both original inputs. No unary volume clock is supplied. -/
theorem add_runs (n volume t : ℕ) :
    HoareTime addProgram (fun v => v=bank n volume (some t))
      (fun v => v=bank n volume (some (t+volume))) (addCost t volume) := by
  have hh := BinaryDescriptorAdvance.advances_hoare (q:=2) (bits t) (bits volume) volume
    (RecursiveChildQuotientsConstant.bits_value volume)
  have he : GrowingCounterData.advance volume (bits t)=bits (t+volume) :=
    BinaryCanonicalData.value_injective _ _
      (BinaryDescriptorAdvance.canonical _ _ (RecursiveChildQuotientsConstant.bits_canonical _))
      (RecursiveChildQuotientsConstant.bits_canonical _)
      (by rw [BinaryDescriptorAdvance.value,RecursiveChildQuotientsConstant.bits_value,
        RecursiveChildQuotientsConstant.bits_value])
  rw [he] at hh
  have ho : BinaryDescriptorAdvance.input (q:=2) (bits (t+volume)) (bits volume)=
      setTape (BinaryDescriptorAdvance.input (bits t) (bits volume)) (0:Fin 3)
        (RadixZeroFill.encodedBinary (bits (t+volume))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [ho] at hh
  have h := Placement.hoare_at hh addPlacement (bank n volume (some t)) (active n volume t)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [←active n volume t,PlacedDescriptorConstruction.replace_setTape]
  simp only [addPlacement,InjectivePlacement.active_slot,addSlots,Matrix.cons_val_zero]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

attribute [local irreducible] copyProgram addProgram

theorem leaf_runs (n volume : ℕ) :
    HoareTime leafProgram (fun v => v=input n volume) (fun v => v=bank n volume (some (n+volume)))
      (leafCost n volume) := by
  unfold leafProgram
  apply ((copy_runs n volume).seq (add_runs n volume n)).consequence (fun _ h => h) (fun _ h => h)
  unfold leafCost addCost
  omega

theorem network_runs (n volume : ℕ) :
    HoareTime networkProgram (fun v => v=input n volume) (fun v => v=bank n volume (some (n+2*volume)))
      (networkCost n volume) := by
  have h := (leaf_runs n volume).seq (add_runs n volume (n+volume))
  have he : n+volume+volume=n+2*volume := by omega
  simpa only [he,networkProgram,networkCost] using h

/-- The physical stopped-leaf body constructs exactly the certified genuine
leaf endpoint exponent, using its retained full axis-count descriptor. -/
theorem leaf_policy_runs (n k : ℕ) :
    HoareTime leafProgram
      (fun v => v=input n (CompactComplexRecursiveGeometry.arity^k))
      (fun v => v=bank n (CompactComplexRecursiveGeometry.arity^k)
        (some (CompactComplexDenominatorPolicy.leafTarget n k)))
      (leafCost n (CompactComplexRecursiveGeometry.arity^k)) :=
  leaf_runs n (CompactComplexRecursiveGeometry.arity^k)

/-- The physical completed-network body constructs exactly the endpoint
grid from the actual framed-network theorem. Runtime branch selection is
separate; this theorem does not supply a branch decision. -/
theorem network_policy_runs (n k : ℕ) :
    HoareTime networkProgram
      (fun v => v=input n (CompactComplexRecursiveGeometry.arity^(k+1)))
      (fun v => v=bank n (CompactComplexRecursiveGeometry.arity^(k+1))
        (some (CompactComplexDenominatorPolicy.networkTarget n k)))
      (networkCost n (CompactComplexRecursiveGeometry.arity^(k+1))) :=
  network_runs n (CompactComplexRecursiveGeometry.arity^(k+1))

/-- Original input, volume, and all heads are retained; work returns blank. -/
theorem endpoint (n volume targetN : ℕ) :
    (bank n volume (some targetN)).head 0=1 ∧
    (bank n volume (some targetN)).tape 0=RadixZeroFill.encodedBinary (bits n) ∧
    (bank n volume (some targetN)).head 1=1 ∧
    (bank n volume (some targetN)).tape 1=RadixZeroFill.encodedBinary (bits volume) ∧
    (bank n volume (some targetN)).head 2=1 ∧
    (bank n volume (some targetN)).tape 2=RadixZeroFill.encodedBinary (bits targetN) ∧
    (bank n volume (some targetN)).head 3=0 ∧
    (bank n volume (some targetN)).tape 3=(fun _ => blank) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.CompactNativeDenominatorTarget
