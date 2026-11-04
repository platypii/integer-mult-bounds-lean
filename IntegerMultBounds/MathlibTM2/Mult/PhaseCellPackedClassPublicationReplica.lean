module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedClassPublicationSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData

/-! Computed class rows and the fixed-bank transpose's real-row identity supply
all padding and length premises of the existing replica scatter executor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s t B L width C : ℕ} [NeZero s] [NeZero t]
  {batch : PackedExactBatch A s t B L}

def Rows.publicationReplica (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (padded : Fin C → Fin B → List GaussianInt) (ambient : Fin B → List (Fin (A+4)))
    (j : Fin B) : PublicationReplica A :=
  ⟨List.ofFn (fun i => padded i j),g.indices.map (rows.classRows g hkeys j),ambient j⟩

theorem Rows.publicationReplica_valid (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (hlength : L = g.length)
    (hcapacity : batch.records.length ≤ C)
    (padded : Fin C → Fin B → List GaussianInt)
    (hlen : ∀ i j, (padded i j).length = L)
    (hreal : ∀ i j, padded (paddedCoreIndex hcapacity i) j = rows.values i j)
    (ambient : Fin B → List (Fin (A+4)))
    (hambient : ∀ j, (ambient j).length = s*batch.W) (j : Fin B) :
    (rows.publicationReplica g hkeys padded ambient j).Valid
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      batch.W (C-batch.records.length) := by
  constructor
  · simp [Rows.publicationReplica,coreSubsetPublicationWindows,PublicationWindows.restrict]
  · intro row hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    exact rows.classRows_length g hkeys hwidth j k hk
  · intro row hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact (hlen i j).trans hlength
  · simp only [Rows.publicationReplica,List.length_map,List.length_ofFn]
    rw [class_key_count g hkeys]
    omega
  · change (List.ofFn (fun i => padded i j)).flatten.drop ((C-batch.records.length)*g.length) = _
    rw [←hlength,paddedArchiveRows_drop hcapacity rows.values padded hlen hreal j,
      ←rows.classRows_map g hkeys j]
    rfl
  · exact hambient j


/-- The runtime replica's output is exactly the class scatter used by the
accuracy and reserved-coordinate theorems. -/
theorem Rows.publicationReplica_output (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices) (hw : 0 < width)
    (padded : Fin C → Fin B → List GaussianInt) (ambient : Fin B → List (Fin (A+4))) (j : Fin B) :
    (rows.publicationReplica g hkeys padded ambient j).output
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist) batch.W =
      g.output batch.W hw (rows.classRows g hkeys j) (ambient j) := rfl

theorem Rows.publicationReplica_word_preserves (rows : batch.Rows) (g : CorePublicationClass s width)
    (hkeys : batch.records.map (fun r => r.k) = g.indices)
    (hwidth : ∀ r ∈ batch.records, r.coreWidth = width) (hw : 0 < width)
    (padded : Fin C → Fin B → List GaussianInt) (ambient : Fin B → List (Fin (A+4)))
    (hambient : ∀ j, (ambient j).length = s*batch.W) (j : Fin B)
    (k : ℕ) (hnot : k ∉ g.indices) (i : ZMod s) (hi : i ∈ ownedCore s width k) :
    (((rows.publicationReplica g hkeys padded ambient j).output
      (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist) batch.W).drop (i.val*batch.W)).take batch.W =
      ((ambient j).drop (i.val*batch.W)).take batch.W := by
  rw [rows.publicationReplica_output g hkeys hw padded ambient j]
  apply coreSubsetPublication_word_preserves width g.length batch.W hw g.indices g.sublist
  · exact (hambient j).ge
  · rw [g.source_length batch.W (rows.classRows g hkeys j) (rows.classRows_length g hkeys hwidth j)]
  · exact hnot
  · exact hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedExactBatch
