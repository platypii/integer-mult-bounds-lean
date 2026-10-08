import IntegerMultBounds.Networks.MaskDAG

/-! Small vertex signatures for certified source-support DAGs. Each addition
intersects common-vertex masks and unions covered-vertex masks, so checking a
signature never scans the much wider source mask. Static banks are checked
against sequential rows and are not trusted as independent oracles. -/

namespace IntegerMultBounds.Networks.MaskSignature

open DisjointCircuit MaskDAG

variable {width vertices : ℕ}

structure Signature (vertices : ℕ) where
  core : BitVec vertices
  union : BitVec vertices
  deriving DecidableEq

/-- Vertices shared by every source payload; the empty intersection is full. -/
def core (payload : Fin width → Finset (Fin vertices)) (support : Finset (Fin width)) :
    Finset (Fin vertices) := Finset.univ.filter (fun v => ∀ i ∈ support, v ∈ payload i)

/-- Vertices appearing in at least one source payload. -/
def union (payload : Fin width → Finset (Fin vertices)) (support : Finset (Fin width)) :
    Finset (Fin vertices) := support.biUnion payload

@[simp] theorem core_singleton (payload : Fin width → Finset (Fin vertices)) (i : Fin width) :
    core payload {i} = payload i := by ext v; simp [core]

@[simp] theorem union_singleton (payload : Fin width → Finset (Fin vertices)) (i : Fin width) :
    union payload {i} = payload i := by simp [union]

@[simp] theorem core_union (payload : Fin width → Finset (Fin vertices))
    (left right : Finset (Fin width)) :
    core payload (left ∪ right) = core payload left ∩ core payload right := by
  ext v
  simp only [core, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_inter]
  aesop

@[simp] theorem union_union (payload : Fin width → Finset (Fin vertices))
    (left right : Finset (Fin width)) :
    union payload (left ∪ right) = union payload left ∪ union payload right := by
  ext v
  simp [union]
  aesop

/-- The two summaries describe the actual certified source support. -/
def Correct (payload : Fin width → Finset (Fin vertices))
    (entry : Entry width) (signature : Signature vertices) : Prop :=
  decode signature.core = core payload (decode entry.mask) ∧
    decode signature.union = union payload (decode entry.mask)

/-- Source payloads are small masks. Parent lookups use two independent static
banks, each checked at the current row before it can be used by later rows. -/
def checkAt (source : Fin width → BitVec vertices)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (offset : ℕ)
    (entry : Entry width) (signature : Signature vertices) : Bool :=
  decide (coreBank offset = some signature.core ∧ unionBank offset = some signature.union) &&
    match entry.kind with
    | .input i => decide (signature.core = source i ∧ signature.union = source i)
    | .add l r =>
      if l < offset ∧ r < offset then
        match coreBank l, coreBank r, unionBank l, unionBank r with
        | some lc, some rc, some lu, some ru =>
          decide (signature.core = lc &&& rc ∧ signature.union = lu ||| ru)
        | _, _, _, _ => false
      else false

/-- Aligned sequential rows; unequal lengths are rejected. -/
def checkChunk (source : Fin width → BitVec vertices)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) :
    ℕ → List (Entry width) → List (Signature vertices) → Bool
  | _, [], [] => true
  | offset, entry :: entries, signature :: signatures =>
    checkAt source coreBank unionBank offset entry signature &&
      checkChunk source coreBank unionBank (offset+1) entries signatures
  | _, _, _ => false

/-- Previously checked bank positions carry their exact semantic summaries. -/
def Meaning (payload : Fin width → Finset (Fin vertices))
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (prior : List (Finset (Fin width))) : Prop :=
  ∀ i (hi : i < prior.length),
    (coreBank i).map decode = some (core payload prior[i]) ∧
      (unionBank i).map decode = some (union payload prior[i])

/-- An accepted summary row is correct using only the certified DAG rule and
semantics of earlier bank positions. -/
theorem checkAt_sound (payload : Fin width → Finset (Fin vertices))
    (source : Fin width → BitVec vertices) (hs : ∀ i, decode (source i) = payload i)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (prior : List (Finset (Fin width)))
    (entry : Entry width) (signature : Signature vertices)
    (hm : Meaning payload coreBank unionBank prior) (hv : entry.toNode.Valid prior)
    (hc : checkAt source coreBank unionBank prior.length entry signature = true) :
    Correct payload entry signature ∧
      coreBank prior.length = some signature.core ∧ unionBank prior.length = some signature.union := by
  obtain ⟨hb, hc⟩ := Bool.and_eq_true_iff.mp hc
  refine ⟨?_, of_decide_eq_true hb⟩
  cases entry with
  | mk kind mask =>
    cases kind with
    | input i =>
      have he : signature.core = source i ∧ signature.union = source i := of_decide_eq_true hc
      have hv' : decode mask = {i} := hv
      simp [Correct, hv', he.1, he.2, hs]
    | add l r =>
      change (if l < prior.length ∧ r < prior.length then _ else false) = true at hc
      split at hc
      next hlt =>
        obtain ⟨hlc, hlu⟩ := hm l hlt.1
        obtain ⟨hrc, hru⟩ := hm r hlt.2
        have hv' : decode mask = prior[l] ∪ prior[r] := by
          have hh : Disjoint prior[l] prior[r] ∧ decode mask = prior[l] ∪ prior[r] := by
            simpa [Entry.toNode, Node.Valid, hlt.1, hlt.2] using hv
          exact hh.2
        cases hcl : coreBank l with
        | none => simp [hcl] at hc
        | some lc =>
          cases hcr : coreBank r with
          | none => simp [hcl, hcr] at hc
          | some rc =>
            cases hul : unionBank l with
            | none => simp [hcl, hcr, hul] at hc
            | some lu =>
              cases hur : unionBank r with
              | none => simp [hcl, hcr, hul, hur] at hc
              | some ru =>
                have he : signature.core = lc &&& rc ∧ signature.union = lu ||| ru := by
                  simpa [hcl, hcr, hul, hur] using hc
                simp only [hcl, hcr, hul, hur, Option.map_some, Option.some.injEq] at hlc hrc hlu hru
                simp [Correct, hv', he.1, he.2, hlc, hrc, hlu, hru]
      next => simp at hc

theorem meaning_append (payload : Fin width → Finset (Fin vertices))
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (prior : List (Finset (Fin width)))
    (entry : Entry width) (signature : Signature vertices)
    (hm : Meaning payload coreBank unionBank prior) (he : Correct payload entry signature)
    (hc : coreBank prior.length = some signature.core)
    (hu : unionBank prior.length = some signature.union) :
    Meaning payload coreBank unionBank (prior ++ [decode entry.mask]) := by
  intro i hi
  by_cases hp : i < prior.length
  · simpa only [List.getElem_append_left hp] using hm i hp
  · have hi' : i = prior.length := by simp only [List.length_append, List.length_singleton] at hi; omega
    subst i
    simpa [hc, hu, Correct] using he

/-- The semantic invariant and every row's correctness advance together. -/
theorem checkChunk_sound (payload : Fin width → Finset (Fin vertices))
    (source : Fin width → BitVec vertices) (hs : ∀ i, decode (source i) = payload i)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (prior : List (Finset (Fin width)))
    (entries : List (Entry width)) (signatures : List (Signature vertices))
    (hm : Meaning payload coreBank unionBank prior)
    (hv : ValidFrom prior (entries.map Entry.toNode))
    (hc : checkChunk source coreBank unionBank prior.length entries signatures = true) :
    List.Forall₂ (Correct payload) entries signatures ∧
      Meaning payload coreBank unionBank (prior ++ entries.map (fun e => decode e.mask)) := by
  induction entries generalizing prior signatures with
  | nil =>
    cases signatures with
    | nil => exact ⟨.nil, by simpa using hm⟩
    | cons signature signatures => simp [checkChunk] at hc
  | cons entry entries ih =>
    cases signatures with
    | nil => simp [checkChunk] at hc
    | cons signature signatures =>
      obtain ⟨hc, ht⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨he, hcb, hub⟩ := checkAt_sound payload source hs coreBank unionBank prior entry signature hm hv.1 hc
      have hn := ih (prior ++ [decode entry.mask]) signatures
        (meaning_append payload coreBank unionBank prior entry signature hm he hcb hub) hv.2
        (by simpa using ht)
      refine ⟨.cons he hn.1, ?_⟩
      simpa [List.append_assoc] using hn.2

/-- Accepted source masks and small signatures certify exact endpoint summaries
for every literal DAG node, without scanning source bits in the summary check. -/
theorem checkChunk_correct (payload : Fin width → Finset (Fin vertices))
    (source : Fin width → BitVec vertices) (hs : ∀ i, decode (source i) = payload i)
    (maskBank : ℕ → Option (BitVec width)) (coreBank unionBank : ℕ → Option (BitVec vertices))
    (entries : List (Entry width)) (signatures : List (Signature vertices))
    (hv : MaskDAG.checkChunk maskBank 0 entries = true)
    (hc : checkChunk source coreBank unionBank 0 entries signatures = true) :
    List.Forall₂ (Correct payload) entries signatures ∧
      Meaning payload coreBank unionBank (entries.map (fun e => decode e.mask)) := by
  simpa using checkChunk_sound payload source hs coreBank unionBank [] entries signatures
    (by intro i hi; simp at hi) (MaskDAG.checkChunk_valid maskBank entries hv) hc

theorem checkChunk_length (source : Fin width → BitVec vertices)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (offset : ℕ)
    (entries : List (Entry width)) (signatures : List (Signature vertices))
    (hc : checkChunk source coreBank unionBank offset entries signatures = true) :
    entries.length = signatures.length := by
  induction entries generalizing offset signatures with
  | nil => cases signatures <;> simp_all [checkChunk]
  | cons entry entries ih =>
    cases signatures with
    | nil => simp [checkChunk] at hc
    | cons signature signatures =>
      have hh := ih (offset+1) signatures (Bool.and_eq_true_iff.mp hc).2
      simpa using hh

/-- Independently reduced summary chunks compose using absolute row indices. -/
theorem checkChunk_append (source : Fin width → BitVec vertices)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (offset : ℕ)
    (first rest : List (Entry width)) (firstS restS : List (Signature vertices))
    (hlen : first.length = firstS.length) :
    checkChunk source coreBank unionBank offset (first ++ rest) (firstS ++ restS) =
      (checkChunk source coreBank unionBank offset first firstS &&
        checkChunk source coreBank unionBank (offset + first.length) rest restS) := by
  induction first generalizing offset firstS with
  | nil =>
    have he : firstS = [] := List.length_eq_zero_iff.mp hlen.symm
    simp [he, checkChunk]
  | cons entry first ih =>
    cases firstS with
    | nil => simp at hlen
    | cons signature firstS =>
      have hh := ih (offset+1) firstS (by simpa using hlen)
      simpa [checkChunk, Bool.and_assoc, Nat.add_assoc, Nat.add_comm] using
        congrArg (fun b => checkAt source coreBank unionBank offset entry signature && b) hh

theorem checkChunk_append_of (source : Fin width → BitVec vertices)
    (coreBank unionBank : ℕ → Option (BitVec vertices)) (offset : ℕ)
    (first rest : List (Entry width)) (firstS restS : List (Signature vertices))
    (hf : checkChunk source coreBank unionBank offset first firstS = true)
    (hr : checkChunk source coreBank unionBank (offset + first.length) rest restS = true) :
    checkChunk source coreBank unionBank offset (first ++ rest) (firstS ++ restS) = true := by
  rw [checkChunk_append source coreBank unionBank offset first rest firstS restS
    (checkChunk_length source coreBank unionBank offset first firstS hf), hf, hr]
  rfl

/-- A requested static-bank signature has the exact core and union of its
source support, even when no row list is evaluated by the caller. -/
theorem bank_correct (payload : Fin width → Finset (Fin vertices))
    (source : Fin width → BitVec vertices) (hs : ∀ i, decode (source i) = payload i)
    (maskBank : ℕ → Option (BitVec width)) (coreBank unionBank : ℕ → Option (BitVec vertices))
    (entries : List (Entry width)) (signatures : List (Signature vertices))
    (hv : MaskDAG.checkChunk maskBank 0 entries = true)
    (hc : checkChunk source coreBank unionBank 0 entries signatures = true)
    (i : ℕ) (hi : i < entries.length) :
    (coreBank i).map decode = (maskBank i).map (fun mask => core payload (decode mask)) ∧
      (unionBank i).map decode = (maskBank i).map (fun mask => union payload (decode mask)) := by
  have hm := (checkChunk_correct payload source hs maskBank coreBank unionBank entries signatures hv hc).2
  obtain ⟨hcore, hunion⟩ := hm i (by simpa using hi)
  have hb := (MaskDAG.checkChunk_sound maskBank [] entries (by intro j hj; simp at hj) hv).2
    i (by simpa using hi)
  have hb' : maskBank i = some entries[i].mask := by simpa [List.getElem?_eq_getElem hi] using hb
  simpa [hb'] using And.intro hcore hunion

end IntegerMultBounds.Networks.MaskSignature
