import IntegerMultBounds.Networks.DisjointCircuit
import Mathlib.Data.BitVec

/-! A kernel-checkable bitmask certificate for disjoint addition DAGs.
The verifier operates only on masks and parent indices. Its soundness theorem
constructs the existing semantic DAG without evaluating its finite sets. -/

namespace IntegerMultBounds.Networks.MaskDAG

open DisjointCircuit

variable {width : ℕ}

/-- Source indices represented by the set bits of a fixed-width mask. -/
def decode (mask : BitVec width) : Finset (Fin width) :=
  Finset.univ.filter (fun i => mask.getLsbD i.val)

@[simp] theorem mem_decode (mask : BitVec width) (i : Fin width) :
    i ∈ decode mask ↔ mask.getLsbD i.val = true := by simp [decode]

@[simp] theorem decode_zero : decode (0 : BitVec width) = ∅ := by
  ext i
  simp

@[simp] theorem decode_or (a b : BitVec width) : decode (a ||| b) = decode a ∪ decode b := by
  ext i
  simp

@[simp] theorem decode_and (a b : BitVec width) : decode (a &&& b) = decode a ∩ decode b := by
  ext i
  simp

theorem decode_injective : Function.Injective (decode (width := width)) := by
  intro a b he
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  apply Bool.eq_iff_iff.mpr
  simpa only [mem_decode] using Finset.ext_iff.mp he ⟨i, hi⟩

@[simp] theorem and_eq_zero_iff (a b : BitVec width) :
    a &&& b = 0 ↔ Disjoint (decode a) (decode b) := by
  rw [Finset.disjoint_iff_inter_eq_empty, ← decode_and, ← decode_zero]
  exact ⟨congrArg decode, fun h => decode_injective h⟩

/-- The exact singleton input mask. -/
def singleton (i : Fin width) : BitVec width := BitVec.ofNat width 1 <<< i.val

@[simp] theorem decode_singleton (i : Fin width) : decode (singleton i) = {i} := by
  ext j
  simp only [mem_decode, singleton, BitVec.getLsbD_shiftLeft,
    Finset.mem_singleton, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  have hi := i.isLt
  have hj := j.isLt
  rw [Fin.ext_iff]
  have hone := @BitVec.getLsbD_one width (j.val - i.val)
  rw [hone]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- Support masks are explicit certificate data; their meaning is checked. -/
structure Entry (width : ℕ) where
  kind : Kind (Fin width)
  mask : BitVec width
  deriving DecidableEq

def Entry.toNode (entry : Entry width) : Node (Fin width) :=
  ⟨entry.kind, decode entry.mask⟩

/-- Only backward references may be read from the already checked bank. -/
def checkEntry (prior : Array (BitVec width)) (entry : Entry width) : Bool :=
  match entry.kind with
  | .input i => decide (entry.mask = singleton i)
  | .add l r =>
    if hl : l < prior.size then
      if hr : r < prior.size then
        decide (prior[l] &&& prior[r] = 0) && decide (entry.mask = prior[l] ||| prior[r])
      else false
    else false

theorem checkEntry_sound (prior : Array (BitVec width)) (entry : Entry width)
    (hc : checkEntry prior entry = true) :
    entry.toNode.Valid (prior.toList.map decode) := by
  cases entry with
  | mk kind mask =>
    cases kind with
    | input i =>
      have he : mask = singleton i := by simpa [checkEntry] using hc
      simp [Entry.toNode, Node.Valid, he]
    | add l r =>
      simp only [checkEntry] at hc
      split at hc
      next hl =>
        split at hc
        next hr =>
          obtain ⟨hd, he⟩ := Bool.and_eq_true_iff.mp hc
          have hd' := (and_eq_zero_iff prior[l] prior[r]).mp (of_decide_eq_true hd)
          have he' : mask = prior[l] ||| prior[r] := of_decide_eq_true he
          simpa [Entry.toNode, Node.Valid, hl, hr, he'] using hd'
        next => simp at hc
      next => simp at hc

/-- Sequential validation; array storage avoids scanning a list per parent. -/
def checkFrom (prior : Array (BitVec width)) : List (Entry width) → Bool
  | [] => true
  | entry :: entries => checkEntry prior entry && checkFrom (prior.push entry.mask) entries

def check (entries : List (Entry width)) : Bool := checkFrom #[] entries

/-- The mask bank after a checked chunk, independently of its acceptance. -/
def bankAfter (prior : Array (BitVec width)) (entries : List (Entry width)) : Array (BitVec width) :=
  prior ++ (entries.map Entry.mask).toArray

@[simp] theorem bankAfter_nil (prior : Array (BitVec width)) : bankAfter prior [] = prior := by
  simp [bankAfter]

@[simp] theorem bankAfter_cons (prior : Array (BitVec width)) (entry : Entry width)
    (entries : List (Entry width)) :
    bankAfter prior (entry :: entries) = bankAfter (prior.push entry.mask) entries := by
  apply Array.toList_inj.mp
  simp [bankAfter]

/-- Chunk checks compose without recomputing earlier support certificates. -/
theorem checkFrom_append (prior : Array (BitVec width)) (first rest : List (Entry width)) :
    checkFrom prior (first ++ rest) =
      (checkFrom prior first && checkFrom (bankAfter prior first) rest) := by
  induction first generalizing prior with
  | nil => simp [checkFrom]
  | cons entry first ih => simp [checkFrom, ih, Bool.and_assoc]

theorem checkFrom_append_of (prior : Array (BitVec width)) (first rest : List (Entry width))
    (hfirst : checkFrom prior first = true)
    (hrest : checkFrom (bankAfter prior first) rest = true) :
    checkFrom prior (first ++ rest) = true := by
  rw [checkFrom_append, hfirst, hrest]
  rfl

/-- Accepted mask certificates produce actual semantically valid DAGs. -/
theorem checkFrom_sound (prior : Array (BitVec width)) (entries : List (Entry width))
    (hc : checkFrom prior entries = true) :
    ValidFrom (prior.toList.map decode) (entries.map Entry.toNode) := by
  induction entries generalizing prior with
  | nil => trivial
  | cons entry entries ih =>
    obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp hc
    refine ⟨checkEntry_sound prior entry hc, ?_⟩
    simpa [Array.toList_push, List.map_append, Entry.toNode] using ih (prior.push entry.mask) ht

theorem check_sound (entries : List (Entry width)) (hc : check entries = true) :
    Valid (entries.map Entry.toNode) := by
  simpa [Valid] using checkFrom_sound #[] entries hc

/-- Checked execution computes the sum of exactly the source bits in each mask. -/
theorem eval_eq {A : Type*} [AddCommMonoid A] (input : Fin width → A)
    (entries : List (Entry width)) (hc : check entries = true) :
    DisjointCircuit.eval input (entries.map Entry.toNode) =
      entries.map (fun entry => supportSum input (decode entry.mask)) := by
  simpa only [List.map_map, Function.comp_def, Entry.toNode] using DisjointCircuit.eval_eq input _ (check_sound entries hc)


/-- A static mask bank with user-supplied split indices. No balancing or size
annotation is trusted: agreement with every row is checked separately. -/
inductive Bank (width : ℕ) where
  | empty
  | leaf (mask : BitVec width)
  | branch (pivot : ℕ) (left right : Bank width)

def Bank.lookup : Bank width → ℕ → Option (BitVec width)
  | .empty, _ => none
  | .leaf mask, i => if i = 0 then some mask else none
  | .branch pivot left right, i =>
    if i < pivot then left.lookup i else right.lookup (i - pivot)

/-- The static oracle agrees with the masks already certified in order. -/
def Agrees (bank : ℕ → Option (BitVec width)) (prior : List (BitVec width)) : Prop :=
  ∀ i < prior.length, bank i = prior[i]?

theorem agrees_append (bank : ℕ → Option (BitVec width)) (prior : List (BitVec width))
    (mask : BitVec width) (ha : Agrees bank prior) (hm : bank prior.length = some mask) :
    Agrees bank (prior ++ [mask]) := by
  intro i hi
  by_cases hp : i < prior.length
  · rw [List.getElem?_append_left hp]
    exact ha i hp
  · have he : i = prior.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa using hm

/-- Check a row against a static bank, including its own position. -/
def checkAt (bank : ℕ → Option (BitVec width)) (offset : ℕ) (entry : Entry width) : Bool :=
  decide (bank offset = some entry.mask) &&
    match entry.kind with
    | .input i => decide (entry.mask = singleton i)
    | .add l r =>
      if l < offset ∧ r < offset then
        match bank l, bank r with
        | some a, some b => decide (a &&& b = 0) && decide (entry.mask = a ||| b)
        | _, _ => false
      else false

theorem checkAt_sound (bank : ℕ → Option (BitVec width)) (prior : List (BitVec width))
    (entry : Entry width) (ha : Agrees bank prior) (hc : checkAt bank prior.length entry = true) :
    entry.toNode.Valid (prior.map decode) ∧ bank prior.length = some entry.mask := by
  obtain ⟨hm, hc⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨?_, of_decide_eq_true hm⟩
  cases entry with
  | mk kind mask =>
    cases kind with
    | input i =>
      have he : mask = singleton i := of_decide_eq_true hc
      simp [Entry.toNode, Node.Valid, he]
    | add l r =>
      change (if l < prior.length ∧ r < prior.length then _ else false) = true at hc
      split at hc
      next hp =>
        rw [ha l hp.1, ha r hp.2, List.getElem?_eq_getElem hp.1, List.getElem?_eq_getElem hp.2] at hc
        obtain ⟨hd, he⟩ := Bool.and_eq_true_iff.mp hc
        have hd' := (and_eq_zero_iff prior[l] prior[r]).mp (of_decide_eq_true hd)
        have he' : mask = prior[l] ||| prior[r] := of_decide_eq_true he
        simpa [Entry.toNode, Node.Valid, hp.1, hp.2, he'] using hd'
      next => simp at hc

/-- Independently check a chunk at its absolute starting index. -/
def checkChunk (bank : ℕ → Option (BitVec width)) (offset : ℕ) : List (Entry width) → Bool
  | [] => true
  | entry :: entries => checkAt bank offset entry && checkChunk bank (offset + 1) entries

/-- Both validity and bank agreement advance through a checked chunk. -/
theorem checkChunk_sound (bank : ℕ → Option (BitVec width)) (prior : List (BitVec width))
    (entries : List (Entry width)) (ha : Agrees bank prior)
    (hc : checkChunk bank prior.length entries = true) :
    ValidFrom (prior.map decode) (entries.map Entry.toNode) ∧
      Agrees bank (prior ++ entries.map Entry.mask) := by
  induction entries generalizing prior with
  | nil => simpa [ValidFrom] using ha
  | cons entry entries ih =>
    obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨hv, hm⟩ := checkAt_sound bank prior entry ha hc
    have hnext := ih (prior ++ [entry.mask]) (agrees_append bank prior entry.mask ha hm)
      (by simpa using ht)
    refine ⟨⟨hv, ?_⟩, ?_⟩
    · simpa [Entry.toNode] using hnext.1
    · simpa [List.append_assoc] using hnext.2

/-- Static chunks compose by their indices; the bank is never rebuilt. -/
theorem checkChunk_append (bank : ℕ → Option (BitVec width)) (offset : ℕ)
    (first rest : List (Entry width)) :
    checkChunk bank offset (first ++ rest) =
      (checkChunk bank offset first && checkChunk bank (offset + first.length) rest) := by
  induction first generalizing offset with
  | nil => simp [checkChunk]
  | cons entry first ih => simp [checkChunk, ih, Bool.and_assoc, Nat.add_assoc, Nat.add_comm]

theorem checkChunk_append_of (bank : ℕ → Option (BitVec width)) (offset : ℕ)
    (first rest : List (Entry width))
    (hf : checkChunk bank offset first = true)
    (hr : checkChunk bank (offset + first.length) rest = true) :
    checkChunk bank offset (first ++ rest) = true := by
  rw [checkChunk_append, hf, hr]
  rfl

/-- Any accepted static-bank certificate supplies the existing DAG semantics. -/
theorem checkChunk_valid (bank : ℕ → Option (BitVec width)) (entries : List (Entry width))
    (hc : checkChunk bank 0 entries = true) : Valid (entries.map Entry.toNode) := by
  have hh := checkChunk_sound bank [] entries (by intro i hi; simp at hi) hc
  exact hh.1


/-- An accepted static-bank output is the exact support sum of its bank mask. -/
theorem checkChunk_eval_get {A : Type*} [AddCommMonoid A] (input : Fin width → A)
    (bank : ℕ → Option (BitVec width)) (entries : List (Entry width))
    (hc : checkChunk bank 0 entries = true) (i : ℕ) (hi : i < entries.length) :
    (DisjointCircuit.eval input (entries.map Entry.toNode))[i]? =
      (bank i).map (fun mask => supportSum input (decode mask)) := by
  obtain ⟨hv, ha⟩ := checkChunk_sound bank [] entries (by intro j hj; simp at hj) hc
  have he := ha i (by simpa using hi)
  simp only [List.nil_append] at he
  rw [DisjointCircuit.eval_eq input _ hv, he]
  simp only [List.map_map, List.getElem?_map, Option.map_map, Function.comp_def, Entry.toNode]

end IntegerMultBounds.Networks.MaskDAG
