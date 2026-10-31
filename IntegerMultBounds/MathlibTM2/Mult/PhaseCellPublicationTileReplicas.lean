module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData

/-! The transpose's returned coefficient rows directly supply the publication
ledger. No second encoding or independent execution witness is required. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

def publicationTileReplica {A N C B : ℕ}
    (rows : Fin N → Fin B → List GaussianInt)
    (paddedRows : Fin C → Fin B → List GaussianInt)
    (ambient : Fin B → List (Fin (A+4))) (j : Fin B) : PublicationReplica A where
  paddedRows := List.ofFn (fun i => paddedRows i j)
  rows := List.ofFn (fun i => rows i j)
  ambient := ambient j

theorem publicationTileReplica_valid {A s L N C B : ℕ}
    (windows : PublicationWindows s L) (w : ℕ) (hN : N ≤ C)
    (hcount : N = windows.origins.length)
    (rows : Fin N → Fin B → List GaussianInt)
    (paddedRows : Fin C → Fin B → List GaussianInt)
    (ambient : Fin B → List (Fin (A+4)))
    (hlen : ∀ i j, (rows i j).length = L)
    (hpadded : ∀ i j, (paddedRows i j).length = L)
    (hreal : ∀ i j, paddedRows (paddedCoreIndex hN i) j = rows i j)
    (hambient : ∀ j, (ambient j).length = s*w) (j : Fin B) :
    (publicationTileReplica rows paddedRows ambient j).Valid windows w (C-N) := by
  refine ⟨?_,?_,?_,?_,?_,hambient j⟩
  · simpa [publicationTileReplica] using hcount
  · intro row hr
    obtain ⟨i,he⟩ := List.mem_ofFn.mp hr
    subst row
    exact hlen i j
  · intro row hr
    obtain ⟨i,he⟩ := List.mem_ofFn.mp hr
    subst row
    exact hpadded i j
  · simp only [publicationTileReplica,List.length_ofFn]
    omega
  · exact paddedArchiveRows_drop hN rows paddedRows hpadded hreal j

theorem publicationTileReplicas_input {A N C B : ℕ} (w : ℕ)
    (rows : Fin N → Fin B → List GaussianInt)
    (paddedRows : Fin C → Fin B → List GaussianInt)
    (ambient : Fin B → List (Fin (A+4))) :
    (List.ofFn (publicationTileReplica rows paddedRows ambient)).flatMap (PublicationReplica.input w) =
      (List.ofFn fun j => cstream A w (List.ofFn fun i => paddedRows i j).flatten).flatten := by
  simp only [List.flatMap,List.map_ofFn,Function.comp_def,PublicationReplica.input,publicationTileReplica]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
