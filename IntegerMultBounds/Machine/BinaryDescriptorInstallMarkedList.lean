import IntegerMultBounds.Machine.BinaryDescriptorInstall
import IntegerMultBounds.Machine.ExactFrame

/-! A fixed list of physical marked descriptor installations, with every copy,
marker construction, and sequential join charged. The source bank is preserved and
no descriptor value enters the compiled transition table. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList
open SharedPlacementAlphabet (setTape)
variable {t q : ℕ}

structure Instruction (t : ℕ) where
  source : Fin t
  dest : Fin t
  distinct : source ≠ dest

/-- No destination may overwrite any source, including a later source. -/
def Disjoint (ops : List (Instruction t)) : Prop :=
  ∀ a ∈ ops, ∀ b ∈ ops, a.dest ≠ b.source

def Unique (ops : List (Instruction t)) : Prop := (ops.map Instruction.dest).Nodup

def write (op : Instruction t) (xs : Fin t → List Bool) (v : Tapes t q) : Tapes t q :=
  setTape v op.dest (RadixZeroFill.encodedBinary (xs op.source)) 1

/-- Exact final bank, with no implicit copying or normalization. -/
def result : List (Instruction t) → (Fin t → List Bool) → Tapes t q → Tapes t q
  | [],_,v => v
  | op::ops,xs,v => result ops xs (write op xs v)

theorem result_foldl (ops : List (Instruction t)) (xs : Fin t → List Bool) (v : Tapes t q) :
    result ops xs v = ops.foldl (fun v op => write op xs v) v := by
  induction ops generalizing v with
  | nil => rfl
  | cons op ops ih => exact ih _

def states : List (Instruction t) → ℕ
  | [] => 1
  | _::ops => 5+states ops

theorem states_eq (ops : List (Instruction t)) : states ops = 5*ops.length+1 := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp only [states,List.length_cons,ih]; omega

noncomputable def program (q : ℕ) (ht : 0 < t) : (ops : List (Instruction t)) → Program t (states ops) q
  | [] => skip t q ht
  | op::ops => seq (BinaryDescriptorInstall.program q op.source op.dest op.distinct) (program q ht ops)

/-- One extra step per instruction pays the real join into the remaining list. -/
def cost (ops : List (Instruction t)) (xs : Fin t → List Bool) : ℕ :=
  (ops.map (fun op => 2*(xs op.source).length+6)).sum

theorem result_frame (ops : List (Instruction t)) (xs : Fin t → List Bool) (v : Tapes t q)
    (i : Fin t) (hi : ∀ op ∈ ops, i ≠ op.dest) :
    (result ops xs v).head i = v.head i ∧ (result ops xs v).tape i = v.tape i := by
  induction ops generalizing v with
  | nil => exact ⟨rfl,rfl⟩
  | cons op ops ih =>
    have hh := ih (write op xs v) (fun a ha => hi a (List.mem_cons_of_mem _ ha))
    have hn := hi op (List.mem_cons_self)
    simpa only [result,write,setTape,Function.update_of_ne hn] using hh

/-- Every selected destination has its exact marked word and descriptor head. -/
theorem result_dest (ops : List (Instruction t)) (hu : Unique ops)
    (xs : Fin t → List Bool) (v : Tapes t q) (op : Instruction t) (hop : op ∈ ops) :
    (result ops xs v).head op.dest = 1 ∧
    (result ops xs v).tape op.dest = RadixZeroFill.encodedBinary (xs op.source) := by
  induction ops generalizing v with
  | nil => exact (List.not_mem_nil hop).elim
  | cons a ops ih =>
    have hh : a.dest ∉ ops.map Instruction.dest ∧ Unique ops := by
      simpa only [Unique,List.map_cons,List.nodup_cons] using hu
    rcases List.mem_cons.mp hop with rfl | hop
    · have hf := result_frame ops xs (write op xs v) op.dest (by
        intro b hb he
        exact hh.1 (List.mem_map.mpr ⟨b,hb,he.symm⟩))
      simpa only [result,write,setTape,Function.update_self] using hf
    · exact ih hh.2 (write a xs v) hop

/-- Concrete whole-bank contract. Source descriptors may be shared by any
number of installations, while destination slots must be distinct. -/
theorem installs_hoare (ht : 0 < t) (ops : List (Instruction t))
    (hdis : Disjoint ops) (huniq : Unique ops) (xs : Fin t → List Bool) (v : Tapes t q)
    (hsrc : ∀ op ∈ ops, v.head op.source = 1 ∧ v.tape op.source = RadixZeroFill.encodedBinary (xs op.source))
    (hdst : ∀ op ∈ ops, v.head op.dest = 0 ∧ v.tape op.dest = fun _ => blank) :
    HoareTime (program q ht ops) (fun w => w = v) (fun w => w = result ops xs v) (cost ops xs) := by
  induction ops generalizing v with
  | nil => exact skip_hoare ht v
  | cons op ops ih =>
    have hsrc0 := hsrc op (List.mem_cons_self)
    have hdst0 := hdst op (List.mem_cons_self)
    have hdisTail : Disjoint ops := fun a ha b hb =>
      hdis a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    have hu : op.dest ∉ ops.map Instruction.dest ∧ Unique ops := by
      simpa only [Unique,List.map_cons,List.nodup_cons] using huniq
    have hsrcTail : ∀ a ∈ ops, (write op xs v).head a.source = 1 ∧
        (write op xs v).tape a.source = RadixZeroFill.encodedBinary (xs a.source) := by
      intro a ha
      have hn := (hdis op (List.mem_cons_self) a (List.mem_cons_of_mem _ ha)).symm
      simpa only [write,setTape,Function.update_of_ne hn] using hsrc a (List.mem_cons_of_mem _ ha)
    have hdstTail : ∀ a ∈ ops, (write op xs v).head a.dest = 0 ∧
        (write op xs v).tape a.dest = fun _ => blank := by
      intro a ha
      have hn : a.dest ≠ op.dest := by
        intro he
        exact hu.1 (List.mem_map.mpr ⟨a,ha,he⟩)
      simpa only [write,setTape,Function.update_of_ne hn] using hdst a (List.mem_cons_of_mem _ ha)
    have hf := BinaryDescriptorInstall.install_hoare op.source op.dest op.distinct v (xs op.source)
      hsrc0.2 hsrc0.1 hdst0.2 hdst0.1
    have hh := hf.seq (ih hdisTail hu.2 (write op xs v) hsrcTail hdstTail)
    apply hh.consequence (fun _ h => h) (fun _ h => h) ?_
    simp only [cost,List.map_cons,List.sum_cons]
    omega

/-- A uniform descriptor-width bound gives a uniform bound for the fixed list. -/
theorem cost_le (ops : List (Instruction t)) (xs : Fin t → List Bool) (L : ℕ)
    (h : ∀ op ∈ ops, (xs op.source).length ≤ L) : cost ops xs ≤ ops.length*(2*L+6) := by
  induction ops with
  | nil => simp [cost]
  | cons op ops ih =>
    have h0 := h op List.mem_cons_self
    have hh := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

end IntegerMultBounds.Machine.BinaryDescriptorInstallMarkedList
