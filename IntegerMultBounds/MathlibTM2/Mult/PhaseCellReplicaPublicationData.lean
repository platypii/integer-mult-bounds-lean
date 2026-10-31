module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedWindowPublication

/-! The replica ledger describes owned input and ambient lines. It does not
supply execution witnesses or precomputed publication-control tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure PublicationReplica (A : ℕ) where
  paddedRows : List (List GaussianInt)
  rows : List (List GaussianInt)
  ambient : List (Fin (A+4))

namespace PublicationReplica
variable {A s L : ℕ}

def input (w : ℕ) (r : PublicationReplica A) := cstream A w r.paddedRows.flatten

def words (w : ℕ) (r : PublicationReplica A) := cstream A w r.rows.flatten

def output (windows : PublicationWindows s L) (w : ℕ) (r : PublicationReplica A) :=
  scatterRows (L*w) r.ambient (r.words w) (windows.gaps w)

structure Valid (windows : PublicationWindows s L) (w missing : ℕ) (r : PublicationReplica A) : Prop where
  rowCount : r.rows.length = windows.origins.length
  rowLength : ∀ row ∈ r.rows, row.length = L
  paddedLength : ∀ row ∈ r.paddedRows, row.length = L
  paddingCount : missing+r.rows.length = r.paddedRows.length
  realRows : r.paddedRows.flatten.drop (missing*L) = r.rows.flatten
  ambientLength : r.ambient.length = s*w

theorem Valid.words_length {windows : PublicationWindows s L} {w missing : ℕ} {r : PublicationReplica A}
    (h : r.Valid windows w missing) :
    (r.words w).length = windows.origins.length*(L*w) := by
  rw [words,length_cstream,length_flatten_const r.rows h.rowLength,h.rowCount,Nat.mul_assoc]

theorem Valid.output_length {windows : PublicationWindows s L} {w missing : ℕ} {r : PublicationReplica A}
    (h : r.Valid windows w missing) : (r.output windows w).length = s*w := by
  rw [output,length_scatterRows,h.ambientLength]
  · exact windows.gaps_fits w r.ambient (by rw [h.ambientLength])
  · rw [PublicationWindows.gaps_length,h.words_length]

theorem Valid.output_source_suffix {windows : PublicationWindows s L} {w missing : ℕ}
    {r : PublicationReplica A} (h : r.Valid windows w missing) (tail : List (Fin (A+4))) :
    scatterRows (L*w) r.ambient (r.words w++tail) (windows.gaps w) =
      r.output windows w := by
  apply scatterRows_source_suffix
  rw [PublicationWindows.gaps_length,h.words_length]

end PublicationReplica
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
