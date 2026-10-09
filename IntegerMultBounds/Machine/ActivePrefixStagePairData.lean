import IntegerMultBounds.Machine.ActivePrefixStageRuntimeSelected
import IntegerMultBounds.Machine.ActivePrefixStageSlotRewrite
import IntegerMultBounds.Networks.BinaryRowProgram

/-! A literal binary row addition changes only original source/target header
words. All node geometry and the complete raw array remain in place. -/
namespace IntegerMultBounds.Machine.ActivePrefixStagePairData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs original)
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixStageRuntimeProgram (bank count)
open Networks.BinaryRowProgram (Op)
open RecursiveChildQuotientsConstant (bits)
open ActivePrefixStageSlotRewrite (updated)
variable {s : Shape}

abbrev changePair (d : Inputs s) (op : Op (Fin d.stage.slots)) : Inputs s :=
  {d with stage:={d.stage with source:=op.source,target:=op.target,distinct:=op.distinct.symm}}

def focus : Fin 2 → Fin count := fun i => ActivePrefixStageRuntimeEndpoint.publicSlots
  (if i=0 then 11 else 12)

theorem focus_injective : Function.Injective focus := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals first | rfl | have hv := congrArg Fin.val h; simp [focus,ActivePrefixStageRuntimeEndpoint.publicSlots] at hv

def pairWords (d : Inputs s) : Fin 2 → List Bool := ![bits d.stage.source.val,bits d.stage.target.val]

theorem headers (d : Inputs s) (x : Array s d.rows) (i : Fin 2) :
    (bank d x).head (focus i)=1 ∧
    (bank d x).tape (focus i)=BinaryDescriptorStack.descriptor (pairWords d i) := by
  have h := ActivePrefixStageRuntimeEndpoint.originals d x
  have hh := congrFun (congrArg Tapes.head h) (if i=0 then 11 else 12)
  have ht := congrFun (congrArg Tapes.tape h) (if i=0 then 11 else 12)
  fin_cases i
  all_goals constructor
  all_goals first | exact hh | exact ht.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

theorem unchanged (d : Inputs s) (op : Op (Fin d.stage.slots)) (i : Fin 13)
    (hs : i.val≠11) (ht : i.val≠12) :
    ActivePrefixStageHeadersData.originalValues (changePair d op).stage d.rows i=
      ActivePrefixStageHeadersData.originalValues d.stage d.rows i := by
  fin_cases i <;> simp_all [ActivePrefixStageHeadersData.originalValues,changePair]

theorem original_pair (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows) :
    updated (12:Fin 66) op.target.val (updated (11:Fin 66) op.source.val (original d x))=
      original (changePair d op) x := by
  have he (i : Fin 66) :
      (updated (12:Fin 66) op.target.val (updated (11:Fin 66) op.source.val (original d x))).head i=
        (original (changePair d op) x).head i ∧
      (updated (12:Fin 66) op.target.val (updated (11:Fin 66) op.source.val (original d x))).tape i=
        (original (changePair d op) x).tape i := by
    by_cases h12 : i=12
    · subst i
      have h := ActivePrefixStageFullEndpoint.original_header (changePair d op) x 12
      exact ⟨h.1.symm,(BinaryDescriptorStackRoundtrip.descriptor_encoded _).trans h.2.symm⟩
    by_cases h11 : i=11
    · subst i
      have h := ActivePrefixStageFullEndpoint.original_header (changePair d op) x 11
      simp only [updated,SharedPlacementAlphabet.setTape,Function.update_of_ne (by decide : (11:Fin 66)≠12),
        Function.update_self]
      exact ⟨h.1.symm,(BinaryDescriptorStackRoundtrip.descriptor_encoded _).trans h.2.symm⟩
    simp only [updated,SharedPlacementAlphabet.setTape,Function.update_of_ne h11,Function.update_of_ne h12]
    by_cases hi : i.val<13
    · have ho := ActivePrefixStageFullEndpoint.original_header d x ⟨i.val,hi⟩
      have hn := ActivePrefixStageFullEndpoint.original_header (changePair d op) x ⟨i.val,hi⟩
      have hu := unchanged d op ⟨i.val,hi⟩
        (fun h => h11 (Fin.ext h)) (fun h => h12 (Fin.ext h))
      rw [hu] at hn
      exact ⟨ho.1.trans hn.1.symm,ho.2.trans hn.2.symm⟩
    · by_cases h65 : i=65
      · subst i
        have ho := ActivePrefixStageFullEndpoint.original_raw d x
        have hn := ActivePrefixStageFullEndpoint.original_raw (changePair d op) x
        exact ⟨ho.1.trans hn.1.symm,ho.2.trans hn.2.symm⟩
      · have ho := ActivePrefixStageFullEndpoint.original_blank d x i (by omega) (fun h => h65 (Fin.ext h))
        have hn := ActivePrefixStageFullEndpoint.original_blank (changePair d op) x i (by omega) (fun h => h65 (Fin.ext h))
        exact ⟨ho.1.trans hn.1.symm,ho.2.trans hn.2.symm⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (he i).1
  · funext i; exact (he i).2

theorem bank_pair (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows) :
    updated (focus 1) op.target.val (updated (focus 0) op.source.val (bank d x))=
      bank (changePair d op) x := by
  rw [ActivePrefixStageRuntimeEndpoint.bank_eq_original,ActivePrefixStageRuntimeEndpoint.bank_eq_original]
  have h66 : 66≤count := by unfold count ActivePrefixStageRuntimeProgram.commonCount; omega
  unfold updated
  rw [show focus 0=Fin.castLE h66 (11:Fin 66) from rfl,
    show focus 1=Fin.castLE h66 (12:Fin 66) from rfl,
    ←ActivePrefixEarlySequenceOriginalPlaced.raw_set h66,
    ←ActivePrefixEarlySequenceOriginalPlaced.raw_set h66]
  exact congrArg (fun v => SharedBankStageInput.raw v count) (original_pair d op x)

def program {M : ℕ} (op : Op (Fin M)) := ActivePrefixStageSlotRewrite.pair
  (a:=Networks.Shared50ModularControl.prime) (focus 0) (focus 1) op.source.val op.target.val

def cost (d : Inputs s) (op : Op (Fin d.stage.slots)) :=
  ActivePrefixStageSlotRewrite.cost (bits d.stage.source.val) op.source.val+
    ActivePrefixStageSlotRewrite.cost (bits d.stage.target.val) op.target.val+1

theorem runs (d : Inputs s) (op : Op (Fin d.stage.slots)) (x : Array s d.rows) :
    HoareTime (program op) (fun w => w=bank d x) (fun w => w=bank (changePair d op) x) (cost d op) := by
  have h0 := headers d x 0
  have h1 := headers d x 1
  have h := ActivePrefixStageSlotRewrite.pair_runs (focus 0) (focus 1)
    (fun h => by have := focus_injective h; contradiction) op.source.val op.target.val (bank d x)
    (bits d.stage.source.val) (bits d.stage.target.val) h0.2 h0.1 h1.2 h1.1
  rw [bank_pair] at h
  exact h

end
end IntegerMultBounds.Machine.ActivePrefixStagePairData
