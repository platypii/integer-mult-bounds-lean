import IntegerMultBounds.Machine.BinaryDescriptorFrameRestore
import IntegerMultBounds.Machine.RecursiveHeaderBounds

/-! Erase retained child layout headers and restore a saved ancestor frame,
charging both sets of physical scans to the active child's logical volume. -/
namespace IntegerMultBounds.Machine.RecursiveHeaderRestore
open RecursiveInterchangeLayout RecursiveInterchangeVolume RecursiveDimensionBank
open BinaryDescriptorFrames BinaryDescriptorFrameRestore
variable {t a q roles m n d k : ℕ} {root active ancestor : Descriptor}

theorem cost_le_linear (current : Path q roles m root n active) (olderPath : Path q roles m root d ancestor)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (ops : List (Slot stack)) (field : Slot stack → Fin 6)
    (oldHeaders childHeaders : Fin 6 → List Bool) (ho : Headers ancestor oldHeaders) (hc : Headers active childHeaders)
    (older child : Fin t → List Bool)
    (hops : ∀ i ∈ ops, older i = oldHeaders (field i)) (hcps : ∀ i ∈ ops, child i = childHeaders (field i)) :
    BinaryDescriptorCleanupList.cost (slots ops) child+1+BinaryDescriptorFrames.cost ops older ≤
      (ops.length*(8*(Nat.log2 roles+2)+13)+1)*volume q active := by
  have hclear := BinaryDescriptorCleanupList.cost_le (slots ops) child ((2*(Nat.log2 roles+2))*volume q active) (by
    intro i hi
    obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hi
    rw [hcps op hop]
    exact RecursiveHeaderBounds.header_length_le current hq hr hm hw hv childHeaders hc (field op))
  have hpop := BinaryDescriptorFrames.cost_le ops older ((2*(Nat.log2 roles+2))*volume q active) (by
    intro i hi
    rw [hops i hi]
    exact RecursiveHeaderBounds.saved_header_length_le current olderPath hq hr hm hw hv oldHeaders ho (field i))
  have hp : 0 < volume q active := lt_of_lt_of_le (pow_pos (by omega : 0 < q) _)
    (current.original_chunks (by omega) hr hv)
  simp only [slots,List.length_map] at hclear
  have hsmall : 13*ops.length+1 ≤ (13*ops.length+1)*volume q active := Nat.le_mul_of_pos_right _ hp
  nlinarith

/-- The actual cleanup/pop program starts with retained nonblank child
headers; canonicality and size bounds follow from the two concrete layouts. -/
theorem restore_hoare_linear (current : Path q roles m root n active) (olderPath : Path q roles m root d ancestor)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (ops : List (Slot stack)) (hu : ops.Nodup) (field : Slot stack → Fin 6)
    (oldHeaders childHeaders : Fin 6 → List Bool) (ho : Headers ancestor oldHeaders) (hc : Headers active childHeaders)
    (older child : Fin t → List Bool)
    (hops : ∀ i ∈ ops, older i = oldHeaders (field i)) (hcps : ∀ i ∈ ops, child i = childHeaders (field i))
    (v : Tapes t a)
    (hchild : ∀ i ∈ ops, v.head i = 1 ∧ v.tape i = BinaryDescriptorStack.descriptor (child i))
    (hfree : Free stack ops older v) :
    HoareTime (BinaryDescriptorFrameRestore.program stack ops) (fun w => w = saved stack ops older v)
      (fun w => w = restored ops older v)
      ((ops.length*(8*(Nat.log2 roles+2)+13)+1)*volume q active) :=
  (BinaryDescriptorFrameRestore.restore_hoare stack ops hu older child v hchild hfree).consequence
    (fun _ h => h) (fun _ h => h)
    (cost_le_linear current olderPath hq hr hm hw hv stack ops field oldHeaders childHeaders ho hc older child hops hcps)

/-- Specialized six-field cost, including the join between erase and pop. -/
theorem six_field_cost (current : Path q roles m root n active) (olderPath : Path q roles m root d ancestor)
    (hq : 2 ≤ q) (hr : 0 < roles) (hm : 2 ≤ m) (hw : root.width = m^k) (hv : root.Positive)
    (stack : Fin t) (ops : List (Slot stack)) (hlen : ops.length = 6) (field : Slot stack → Fin 6)
    (oldHeaders childHeaders : Fin 6 → List Bool) (ho : Headers ancestor oldHeaders) (hc : Headers active childHeaders)
    (older child : Fin t → List Bool)
    (hops : ∀ i ∈ ops, older i = oldHeaders (field i)) (hcps : ∀ i ∈ ops, child i = childHeaders (field i)) :
    BinaryDescriptorCleanupList.cost (slots ops) child+1+BinaryDescriptorFrames.cost ops older ≤
      (48*(Nat.log2 roles+2)+79)*volume q active := by
  have h := cost_le_linear current olderPath hq hr hm hw hv stack ops field oldHeaders childHeaders ho hc older child hops hcps
  rw [hlen] at h
  convert h using 1; ring

end IntegerMultBounds.Machine.RecursiveHeaderRestore
