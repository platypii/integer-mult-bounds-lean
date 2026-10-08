import IntegerMultBounds.Networks.Paired49Certificate
import IntegerMultBounds.Networks.SharedPointLift
import IntegerMultBounds.Networks.SharedPointMatching
import IntegerMultBounds.Networks.DisjointUnique

/-! The actual fifty-copy family of certified local addition supports.
Its size is derived from the checked arithmetic count, without reducing a
large semantic finite set or assuming any duplicate-witness facts. -/

namespace IntegerMultBounds.Networks.SharedPointFamily

open DisjointCircuit SharedPointMatching

/-- Input nodes are excluded from the sharing-allocation count. -/
def isAddition {ι : Type*} (node : Node ι) : Bool :=
  match node.kind with | .input _ => false | .add _ _ => true

theorem isAddition_iff {ι : Type*} (node : Node ι) :
    isAddition node = true ↔ ∃ l r, node.kind = .add l r := by
  cases hk : node.kind <;> simp [isAddition, hk]

/-- The identifiers of actual addition nodes in their literal topological list. -/
def additionIds {ι : Type*} (nodes : List (Node ι)) : Finset ℕ :=
  ((nodes.zipIdx.filter (fun row => isAddition row.1)).map Prod.snd).toFinset

theorem mem_additionIds {ι : Type*} (nodes : List (Node ι)) (i : ℕ) :
    i ∈ additionIds nodes ↔ ∃ node, nodes[i]? = some node ∧ ∃ l r, node.kind = .add l r := by
  simp only [additionIds, List.mem_toFinset, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨node,j⟩, ⟨hm, ha⟩, he⟩
    change j = i at he
    subst j
    exact ⟨node, List.mk_mem_zipIdx_iff_getElem?.mp hm, (isAddition_iff node).mp ha⟩
  · rintro ⟨node, hm, ha⟩
    exact ⟨(node,i), ⟨List.mk_mem_zipIdx_iff_getElem?.mpr hm, (isAddition_iff node).mpr ha⟩, rfl⟩

theorem additionIds_bound {ι : Type*} (nodes : List (Node ι)) (i : ℕ) (hi : i ∈ additionIds nodes) :
    i < nodes.length := by
  obtain ⟨node, hn, _⟩ := (mem_additionIds nodes i).mp hi
  exact (List.getElem?_eq_some_iff.mp hn).1

/-- Counting filtered unique indices is exactly counting addition records. -/
theorem additionIds_card {ι : Type*} (nodes : List (Node ι)) :
    (additionIds nodes).card = DAGAllocator.additionCount nodes := by
  have hn : ((nodes.zipIdx).map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hf := hn.sublist (List.filter_sublist.map Prod.snd :
    ((nodes.zipIdx.filter (fun row => isAddition row.1)).map Prod.snd).Sublist _)
  rw [additionIds, List.toFinset_card_of_nodup hf, List.length_map, ← List.countP_eq_length_filter]
  change (nodes.zipIdx.countP (isAddition ∘ Prod.fst)) = nodes.countP isAddition
  rw [← List.countP_map, List.zipIdx_map_fst]

attribute [local irreducible] Paired49Certificate.nodes Certificates.Paired49.entries Certificates.Paired49.bank

/-- Each common point gets one copy of every certified local addition. -/
def domain : Finset (CopyNode 50) :=
  Finset.univ ×ˢ additionIds Paired49Certificate.nodes

/-- The actual source support at a local node; absent indices are empty. -/
def localSupport (i : ℕ) : Finset (Fin 1176) :=
  (Paired49Certificate.nodes[i]?.map Node.support).getD ∅

def support (node : CopyNode 50) : Finset (NeighborCounts.Triple 50) :=
  SharedPointLift.lift49 node.1 (localSupport node.2)

@[simp] theorem mem_domain (node : CopyNode 50) : node ∈ domain ↔ node.2 ∈ additionIds Paired49Certificate.nodes := by
  simp [domain]

theorem mem_domain_iff (node : CopyNode 50) : node ∈ domain ↔
    ∃ localNode, Paired49Certificate.nodes[node.2]? = some localNode ∧
      ∃ l r, localNode.kind = .add l r := by
  rw [mem_domain, mem_additionIds]

/-- Entry-level membership interface for the compact kind classifier. -/
theorem mem_domain_entries (node : CopyNode 50) : node ∈ domain ↔
    ∃ entry, Certificates.Paired49.entries[node.2]? = some entry ∧
      ∃ l r, entry.kind = .add l r := by
  rw [mem_domain_iff]
  simp only [Paired49Certificate.nodes, List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨localNode, ⟨entry, he, hn⟩, l, r, hk⟩
    subst localNode
    exact ⟨entry, he, l, r, hk⟩
  · rintro ⟨entry, he, l, r, hk⟩
    exact ⟨entry.toNode, ⟨entry, he, rfl⟩, l, r, hk⟩

theorem domain_bounds (node : CopyNode 50) (hn : node ∈ domain) : node.2 < 10989 := by
  have hh := additionIds_bound Paired49Certificate.nodes node.2 (mem_domain node |>.mp hn)
  rwa [Paired49Certificate.node_count] at hh

theorem localSupport_get (i : ℕ) (hi : i < Paired49Certificate.nodes.length) :
    localSupport i = Paired49Certificate.nodes[i].support := by
  simp [localSupport, List.getElem?_eq_getElem hi]

/-- The actual local support is the decoded checked static-bank mask. -/
theorem localSupport_bank (i : ℕ) (hi : i < 10989) :
    localSupport i = MaskDAG.decode ((Certificates.Paired49.bank.lookup i).getD 0) := by
  have hb := (MaskDAG.checkChunk_sound Certificates.Paired49.bank.lookup [] Certificates.Paired49.entries
    (by intro j hj; simp at hj) Certificates.Paired49.entries_checked).2 i
    (by simpa only [List.length_append, List.length_nil, zero_add, List.length_map,
      Certificates.Paired49.entries_length] using hi)
  simp only [List.nil_append, List.getElem?_map] at hb
  have he : (Paired49Certificate.nodes[i]?.map Node.support) =
      (Certificates.Paired49.bank.lookup i).map MaskDAG.decode := by
    rw [hb]
    simp only [Paired49Certificate.nodes, List.getElem?_map, Option.map_map,
      Function.comp_def, MaskDAG.Entry.toNode]
  rw [localSupport, he]
  cases Certificates.Paired49.bank.lookup i <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some]
  ext v
  simp [MaskDAG.decode]

theorem support_bank (node : CopyNode 50) (hi : node.2 < 10989) :
    support node = SharedPointLift.lift49 node.1
      (MaskDAG.decode ((Certificates.Paired49.bank.lookup node.2).getD 0)) := by
  rw [support, localSupport_bank node.2 hi]

theorem support_nontrivial (node : CopyNode 50) (hn : node ∈ domain) : 2 ≤ (support node).card := by
  obtain ⟨localNode, hget, l, r, hkind⟩ := (mem_domain_iff node).mp hn
  rw [support, SharedPointLift.lift49_card, localSupport, hget]
  exact DisjointUnique.valid_add_card_two _ Paired49Certificate.valid localNode
    (List.mem_of_getElem? hget) l r hkind

theorem support_common (node : CopyNode 50) (_hn : node ∈ domain)
    (T : NeighborCounts.Triple 50) (hT : T ∈ support node) : node.1 ∈ T.val :=
  SharedPointLift.common_mem _ _ node.1 (localSupport node.2) T hT

theorem support_unique (a : CopyNode 50) (ha : a ∈ domain) (b : CopyNode 50) (hb : b ∈ domain)
    (hc : a.1 = b.1) (he : support a = support b) : a = b := by
  have hi : a.2 < Paired49Certificate.nodes.length := by rw [Paired49Certificate.node_count]; exact domain_bounds a ha
  have hj : b.2 < Paired49Certificate.nodes.length := by rw [Paired49Certificate.node_count]; exact domain_bounds b hb
  have hs : localSupport a.2 = localSupport b.2 := by
    apply SharedPointLift.lift49_injective b.1
    simpa only [support, hc] using he
  rw [localSupport_get a.2 hi, localSupport_get b.2 hj] at hs
  have hs' : (Paired49Certificate.nodes.map Node.support)[a.2]'(by simpa using hi) =
      (Paired49Certificate.nodes.map Node.support)[b.2]'(by simpa using hj) := by simpa using hs
  exact Prod.ext hc (Paired49Certificate.supports_unique.getElem_inj.mp hs')

/-- All structural hypotheses of the duplicate-matching theorem are discharged. -/
def family : Family 50 :=
  ⟨domain, support, support_nontrivial, support_common, support_unique⟩

/-- The unmerged fifty-copy family has exactly fifty times9813 additions. -/
theorem domain_card : domain.card = 50 * 9813 := by
  rw [domain, Finset.card_product, additionIds_card, Paired49Certificate.additions]
  simp

theorem family_domain_card : family.domain.card = 50 * 9813 := domain_card

end IntegerMultBounds.Networks.SharedPointFamily
