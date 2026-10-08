import IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physically replace a fixed list of occupied binary-header slots from a
separate source bank. Old headers are erased before new marked words are copied;
no blank-destination or free-reset assumption is exported. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorReplaceList
open BinaryDescriptorInstallMarkedList
variable {t q : ℕ}
noncomputable section

def destinations (ops : List (Instruction t)) := ops.map Instruction.dest

def program (ht : 0 < t) (ops : List (Instruction t)) :=
  seq (BinaryDescriptorCleanupList.program (a := q) ht (destinations ops))
    (BinaryDescriptorInstallMarkedList.program q ht ops)

def output (ops : List (Instruction t)) (new : Fin t → List Bool) (v : Tapes t q) :=
  result ops new (BinaryDescriptorCleanupList.cleared (destinations ops) v)

def cost (ops : List (Instruction t)) (old new : Fin t → List Bool) :=
  BinaryDescriptorCleanupList.cost (destinations ops) old+1+
    BinaryDescriptorInstallMarkedList.cost ops new

theorem replaces_hoare (ht : 0 < t) (ops : List (Instruction t))
    (hdis : Disjoint ops) (hu : Unique ops) (old new : Fin t → List Bool) (v : Tapes t q)
    (hs : ∀ op ∈ ops, v.head op.source = 1 ∧
      v.tape op.source = RadixZeroFill.encodedBinary (new op.source))
    (hd : ∀ op ∈ ops, v.head op.dest = 1 ∧
      v.tape op.dest = RadixZeroFill.encodedBinary (old op.dest)) :
    HoareTime (program (q := q) ht ops) (fun w => w = v)
      (fun w => w = output ops new v) (cost ops old new) := by
  have he := BinaryDescriptorCleanupList.cleanup_hoare ht (destinations ops) hu old v (by
    intro i hi
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hi
    simpa only [BinaryDescriptorStackRoundtrip.descriptor_encoded] using hd op hop)
  have hi := BinaryDescriptorInstallMarkedList.installs_hoare ht ops hdis hu new
    (BinaryDescriptorCleanupList.cleared (destinations ops) v) (by
      intro op hop
      have hn : op.source ∉ destinations ops := by
        intro hi
        obtain ⟨other,hother,heq⟩ := List.mem_map.mp hi
        exact hdis other hother op hop heq
      have hf := BinaryDescriptorCleanupList.cleared_frame (destinations ops) v op.source hn
      exact ⟨hf.1.trans (hs op hop).1,hf.2.trans (hs op hop).2⟩) (by
      intro op hop
      exact BinaryDescriptorCleanupList.cleared_slot (destinations ops) hu v op.dest
        (List.mem_map.mpr ⟨op,hop,rfl⟩))
  exact he.seq hi

theorem output_dest (ops : List (Instruction t)) (hu : Unique ops)
    (new : Fin t → List Bool) (v : Tapes t q) (op : Instruction t) (hop : op ∈ ops) :
    (output ops new v).head op.dest = 1 ∧
      (output ops new v).tape op.dest = RadixZeroFill.encodedBinary (new op.source) :=
  result_dest ops hu new _ op hop

theorem output_frame (ops : List (Instruction t)) (new : Fin t → List Bool)
    (v : Tapes t q) (i : Fin t) (hi : i ∉ destinations ops) :
    (output ops new v).head i = v.head i ∧ (output ops new v).tape i = v.tape i := by
  have h1 := result_frame ops new (BinaryDescriptorCleanupList.cleared (destinations ops) v) i (by
    intro op hop he
    exact hi (List.mem_map.mpr ⟨op,hop,he.symm⟩))
  have h2 := BinaryDescriptorCleanupList.cleared_frame (destinations ops) v i hi
  exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

/-- All reset, copy and joining transitions are included in the width bound. -/
theorem cost_le (ops : List (Instruction t)) (old new : Fin t → List Bool) (L : ℕ)
    (ho : ∀ op ∈ ops, (old op.dest).length ≤ L)
    (hn : ∀ op ∈ ops, (new op.source).length ≤ L) :
    cost ops old new ≤ ops.length*(4*L+11)+1 := by
  have hc := BinaryDescriptorCleanupList.cost_le (destinations ops) old L (by
    intro i hi
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hi
    exact ho op hop)
  have hi := BinaryDescriptorInstallMarkedList.cost_le ops new L hn
  simp only [destinations,List.length_map] at hc
  unfold cost destinations
  nlinarith

end
end IntegerMultBounds.Machine.BinaryDescriptorReplaceList
