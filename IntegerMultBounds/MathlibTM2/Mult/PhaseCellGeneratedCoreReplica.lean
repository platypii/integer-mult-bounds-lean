module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCorePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData

/-! Derive publication records from generated core rows and the transpose's
padded rows. Only padding relations and row lengths enter the execution ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

def generatedCoreReplica {A : ℕ} (s width L : ℕ) (rows : ℕ → List GaussianInt)
    (padded : List (List GaussianInt)) (ambient : List (Fin (A+4))) : PublicationReplica A where
  paddedRows := padded
  rows := (corePublicationIndices s width L).map rows
  ambient := ambient

theorem generatedCoreReplica_valid {A s : ℕ} (width L w missing : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ coreIndices s width, (rows k).length = coreLength s width k)
    (padded : List (List GaussianInt))
    (hpadded : ∀ row ∈ padded, row.length = L)
    (hcount : missing+(corePublicationIndices s width L).length = padded.length)
    (hdrop : padded.flatten.drop (missing*L) = ((corePublicationIndices s width L).map rows).flatten)
    (ambient : List (Fin (A+4))) (hambient : ambient.length = s*w) :
    (generatedCoreReplica s width L rows padded ambient).Valid (corePublicationWindows s width L hw) w missing := by
  refine ⟨by simp [generatedCoreReplica,corePublicationWindows],?_,hpadded,?_,hdrop,hambient⟩
  · intro row hr
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hr
    subst row
    have hk' := (mem_corePublicationIndices s width L k).mp hk
    exact (hrows k hk'.1).trans hk'.2
  · simpa only [generatedCoreReplica,List.length_map] using hcount

theorem generatedCoreOutput_length {A s : ℕ} (width w : ℕ) (hw : 0 < width)
    (rows : ℕ → List GaussianInt)
    (hrows : ∀ k ∈ coreIndices s width, (rows k).length = coreLength s width k)
    (ambient : List (Fin (A+4))) (hambient : ambient.length = s*w) :
    (generatedCoreOutput (s := s) width w hw rows ambient).length = s*w := by
  have hlength (L : ℕ) : ∀ k ∈ corePublicationIndices s width L, (rows k).length = L := by
    intro k hk
    have hk' := (mem_corePublicationIndices s width L k).mp hk
    exact (hrows k hk'.1).trans hk'.2
  exact coreClassOutput_length width (s%width) w hw rows (hlength _) _
    (coreClassOutput_length width width w hw rows (hlength _) ambient hambient)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
