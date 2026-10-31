module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplit
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSegment
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Schedule
public import IntegerMultBounds.MathlibTM2.M8.Machine.Coordinates

/-!
# The node blocks of a reversed network

The node's blocks on the common bank (`blocks`): the split and merge of `NodeSplit`, a block call
of `NodeCall` at every call site, and for every nonrecursive piece of the schedule an atom
segment (`NodeSegment`), an XOR gate or a zero fill of a wire.

A frame's role streams are its bits on `io`, every other role tape blank (`Good`). The family
serves the frames (`Ok`) of a fixed atom width `b₀` whose rows split over the contract roles at
every depth of the recursion (`depth`), with blank suffixes on their payload, descriptor and PC
stacks. Between the split and the merge the node's bank holds data on the role view with a
blank `io` and bits on every wire (`Node`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode

noncomputable section
open IntegerMultBounds.Machine
open Networks
open Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
open GraphContract (Runs ranks)
open CommonBank (bank K)
open Blocks (seqB seq_runs runs_mono Leading)
open Routines (hdr)
open RecursiveInterchangeLayout (Descriptor volume role)
open RecursiveRoleSerialization (roles)
open NodeBank (tapes io wireSlot wires tempSlot)
open NodePark (childRoles)
open NodeCall (nodeC)
open NodeSplit (midView roleView NodeInv zeroBit)
open SegmentBits (Bits)
open Family (leafC NodeFree Frame)
open Schedule (Seg Call schedule)
open AtomRolePlan (Fits)

variable (N : RevNetwork)

/-! ### Role streams -/

/-- **A frame's role streams**: the bits `x` on `io`, every other role tape blank. -/
def Good (v : Descriptor) (rr : Tapes (tapes N) prime) : Prop :=
  v.Positive ∧ ∃ x : Fin (volume prime v) → ZMod 2,
    rr = childRoles N (RecursiveShiftRoleBank.source (Shared50RecursiveNodeSemantics.encoded x))

theorem bits_encoded {n : ℕ} {a : Fin n → Fin 4} (h : Bits a) :
    ∃ x : Fin n → ZMod 2, a = fun i => SparseRoleCircuit.encode (x i) :=
  ⟨fun i => (h i).choose, funext fun i => (h i).choose_spec⟩

theorem encoded_bits {n : ℕ} (x : Fin n → ZMod 2) : Bits (fun i => SparseRoleCircuit.encode (a := 0) (x i)) :=
  fun i => ⟨x i, rfl⟩

/-! ### The recursion depth -/

/-- The depth of the recursion below a frame of `n` atoms, with fuel. -/
def depthF (m : ℕ) (Rk : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, n => if m ≤ n then 1 + (Rk.map fun r => depthF m Rk k (r * (n / m))).foldr max 0 else 0

/-- The depth of the recursion below a frame of `n` atoms. -/
def depth (m : ℕ) (Rk : List ℕ) (n : ℕ) : ℕ := depthF m Rk n n

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_mono {α : Type} (l : List α) (g g' : α → ℕ) (h : ∀ a ∈ l, g a ≤ g' a) :
    (l.map g).foldr max 0 ≤ (l.map g').foldr max 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (h x List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem depthF_mono (m : ℕ) (Rk : List ℕ) : ∀ k k', k ≤ k' → ∀ n, depthF m Rk k n ≤ depthF m Rk k' n
  | 0, _, _, _ => Nat.zero_le _
  | k+1, 0, h, _ => absurd h (by omega)
  | k+1, k'+1, h, n => by
    simp only [depthF]
    split_ifs
    · exact Nat.add_le_add_left (foldr_max_mono _ _ _ fun r _ => depthF_mono m Rk k k' (by omega) _) _
    · exact le_rfl

/-- A child is at least one level shallower. -/
theorem depth_child {m : ℕ} {Rk : List ℕ} (hRk : ∀ r ∈ Rk, r < m) {n r : ℕ} (hn : m ≤ n) (hr : r ∈ Rk) :
    depth m Rk (r * (n / m)) + 1 ≤ depth m Rk n := by
  have hrm := hRk r hr
  have hm : 0 < m := by omega
  have hf : 1 ≤ n / m := (Nat.one_le_div_iff hm).mpr hn
  have hlt : r * (n / m) ≤ n - 1 := by
    have h1 : r * (n / m) ≤ (m - 1) * (n / m) := Nat.mul_le_mul_right _ (by omega)
    have h2 : m * (n / m) ≤ n := Nat.mul_div_le n m
    have h3 : (m - 1) * (n / m) + n / m = m * (n / m) := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
    omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold depth
  simp only [depthF, hn, ↓reduceIte]
  have := le_foldr_max (List.mem_map.mpr ⟨r, hr, rfl⟩ :
    depthF m Rk k (r * ((k+1) / m)) ∈ Rk.map fun r => depthF m Rk k (r * ((k+1) / m)))
  have hmono := depthF_mono m Rk (r * ((k+1) / m)) k (by omega) (r * ((k+1) / m))
  omega

/-! ### The call stacks -/

/-- The call bank after saving the headers. -/
def sv (hs : Fin 6 → List Bool) (st : Tapes 2 prime) : Tapes 40 prime :=
  BinaryDescriptorFrames.saved RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields
    (RecursiveChildCallSetup.words hs) (RecursiveChildCallSetup.bank hs st)

theorem sv_pc (hs : Fin 6 → List Bool) (st : Tapes 2 prime) :
    (sv hs st).head 39 = st.head 1 ∧ (sv hs st).tape 39 = st.tape 1 := by
  have h := BinaryDescriptorFrames.saved_frame RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields
    (RecursiveChildCallSetup.words hs) (RecursiveChildCallSetup.bank hs st) RecursiveChildCallSetup.pcStack (by decide)
  have h' := CallPlace.bank40_st hs st 1
  exact ⟨h.1.trans h'.1, h.2.trans h'.2⟩

open RecursiveChildCallSetup (savedStacks) in
theorem savedStacks_eq (hs : Fin 6 → List Bool) (st : Tapes 2 prime) {k : ℕ} (code : FiniteReturnStack.Code k) :
    savedStacks hs st code = ⟨![(sv hs st).head 38, (sv hs st).head 39 + k],
      ![(sv hs st).tape 38, FiniteReturnStack.wordPart ((sv hs st).tape 39) ((sv hs st).head 39) code k le_rfl]⟩ := by
  unfold savedStacks RecursiveChildCallSetup.pushed
  change (⟨fun i => (FiniteReturnStackAt.pushed RecursiveChildCallSetup.pcStack code (sv hs st)).head (Fin.natAdd 38 i),
    fun i => (FiniteReturnStackAt.pushed RecursiveChildCallSetup.pcStack code (sv hs st)).tape (Fin.natAdd 38 i)⟩ :
      Tapes 2 prime) = _
  generalize sv hs st = S
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [FiniteReturnStackAt.pushed, SharedPlacementAlphabet.setTape, RecursiveChildCallSetup.pcStack]

open RecursiveChildCallSetup (savedStacks) in
theorem savedStacks_pc (hs : Fin 6 → List Bool) (st : Tapes 2 prime) {k : ℕ} (code : FiniteReturnStack.Code k) :
    (savedStacks hs st code).tape 1 = FiniteReturnStack.wordPart (st.tape 1) (st.head 1) code k le_rfl ∧
      (savedStacks hs st code).head 1 = st.head 1 + k := by
  rw [savedStacks_eq]; simp [(sv_pc hs st).1, (sv_pc hs st).2]

open RecursiveChildCallSetup (savedStacks) in
theorem popped_saved (hs : Fin 6 → List Bool) (st : Tapes 2 prime) {k : ℕ} (code : FiniteReturnStack.Code k) :
    Family.popped (savedStacks hs st code) (st.tape 1) (st.head 1) = savedStacks hs st NodeCall.code0 := by
  rw [savedStacks_eq, savedStacks_eq, FiniteReturnStack.prefix_zero, (sv_pc hs st).1, (sv_pc hs st).2]
  unfold Family.popped SharedPlacementAlphabet.setTape
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> simp

/-! ### The blocks -/

open Classical in

/-- The bank size of an atom segment. -/
def segT (w : N.World ⊕ N.Temp) (l : List (AtomRoleSegment.SOp N.width)) : ℕ :=
  AtomRoleSegment.bankSize (wireSlot N w) l + (tapes N + 15)

theorem segT_ge (w : N.World ⊕ N.Temp) (l : List (AtomRoleSegment.SOp N.width)) :
    ∀ s ∈ l, AtomRoleSegment.tapesOf (wireSlot N w) s ≤ segT N w l :=
  fun s hs => (AtomRoleSegment.bankSize_ge _ _ s hs).trans (Nat.le_add_right _ _)

theorem segT_le (w : N.World ⊕ N.Temp) (l : List (AtomRoleSegment.SOp N.width)) : tapes N + 15 ≤ segT N w l :=
  Nat.le_add_left _ _

/-- The node's ordinary counters are exactly the segment counter ABI. -/
theorem nodeC_segCounters (b f : ℕ) : NodeSegment.SegCounters (nodeC N b f) b f :=
  ⟨by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest],
    by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest], by simp [nodeC],
    by simp [nodeC, Prepare.rest], by simp [nodeC, Prepare.rest], by simp [nodeC]⟩

open Classical in
/-- The XOR gate `dst += src` of a gate of the control. -/
def gateOp (g : Circuit.Gate (N.World ⊕ N.Temp) (ZMod 2)) : List (M8.Machine.RoleOps.Op (tapes N)) :=
  if h : ∃ dst src, dst ≠ src ∧ g = ReversibleFanout.add dst src then
    [.xor ⟨wireSlot N h.choose_spec.choose, wireSlot N h.choose,
      fun he => h.choose_spec.choose_spec.1 (NodeBank.wireSlot_injective N he).symm⟩]
  else []

open Classical in
/-- A nonrecursive piece: an atom segment, an XOR gate or a zero fill. -/
def segB : Seg (N.World ⊕ N.Temp) N.width → Graph.Block (CommonBank.count (tapes N)) prime
  | .edge w ops =>
    if h : ∀ o ∈ AtomSegment.atoms ops, Fits N.width o then
      NodeSegment.place (AtomRoleSegment.chain (segT N w (AtomRoleSegment.sops ops h)) (wireSlot N w)
        (AtomRoleSegment.sops ops h) (segT_ge N w _)).2 (segT_le N w _)
    else NodeBank.ops []
  | .gate g => NodeBank.ops (gateOp N g)
  | .reset w => NodeBank.ops [.fill ⟨io N, wireSlot N w, (NodeBank.wireSlot_ne_io N w).symm⟩ zeroBit]

/-- **The node's blocks.** -/
def blocks (k : ℕ) : Family.NodeBlocks (tapes N) k (Seg (N.World ⊕ N.Temp) N.width) (Call (N.World ⊕ N.Temp)) where
  split := NodeSplit.splitB N
  merge := NodeSplit.mergeB N
  segment := segB N
  enter := fun c code => NodeCall.enterB N c.1 c.2 code
  recover := fun c => NodeCall.recoverB N c.1

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
