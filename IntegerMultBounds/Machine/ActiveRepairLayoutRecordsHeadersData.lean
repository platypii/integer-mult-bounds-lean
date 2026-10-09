import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsEarly
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs
import IntegerMultBounds.Machine.ActiveRepairEarlyKeyOriginalGeometry

/-! Original early caller descriptors determine the full-width record repair
metadata. New words are row length, n+1, source width and complete address width;
their physical construction is the separate header producer. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairRankHeadersEndpoint ActiveRepairRankHeadersData
open RecursiveChildQuotientsConstant (bits bits_value bits_canonical)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def rowBits (d : Inputs s p offset rows) := (d.hs 12).length
def geom (d : Inputs s p offset rows) := geometry s (p.n*p.b) (p.n*p.q)
  p.before p.after offset (p.f*p.q) (rowBits d)
def originals (d : Inputs s p offset rows) : Fin 10 → List Bool :=
  ![d.hs 0,d.hs 1,d.hs 2,d.hs 3,d.hs 4,d.hs 5,d.hs 6,d.hs 11,
    bits (p.n*p.q+p.q),bits (s.bits+rowBits d)]
def sources (d : Inputs s p offset rows) : Fin 4 → List Bool :=
  ![d.hs 7,d.hs 9,d.hs 10,bits (p.n+1)]
def repair (d : Inputs s p offset rows) : ActiveRepairEarlyKeyOriginalData.Data where
  side := .before
  geom := geom d
  originals := originals d
  cs := []
  ss := sources d
  bs := d.hs 8
  q := p.q
  b := p.b
  n := p.n
  rho := p.rho
  f := p.f
  hb := p.hb
  hbq := p.hbq

theorem row_bound (d : Inputs s p offset rows) : rows≤2^rowBits d := by
  have hv := d.hv 12
  change Counter.value (d.hs 12)=rows at hv
  have h := Counter.value_lt (d.hs 12)
  rw [hv] at h
  exact h.le

theorem row_log (d : Inputs s p offset rows) : rowBits d≤rows.log2+1 := by
  have hv := d.hv 12
  change Counter.value (d.hs 12)=rows at hv
  simpa only [rowBits,hv] using GrowingCounterData.canonical_width (d.hs 12) (d.hc 12)

theorem originals_value (d : Inputs s p offset rows) :
    ∀ i, Counter.value (originals d i)=originalValues (geom d) i := by
  intro i
  fin_cases i
  · exact d.hv 0
  · exact d.hv 1
  · exact d.hv 2
  · exact d.hv 3
  · exact d.hv 4
  · exact d.hv 5
  · exact d.hv 6
  · exact d.hv 11
  · change Counter.value (bits (p.n*p.q+p.q))=p.f*p.q
    rw [bits_value,←p.hnf]
    ring
  · exact bits_value _

theorem originals_canonical (d : Inputs s p offset rows) :
    ∀ i, GrowingCounterData.Canonical (originals d i) := by
  intro i
  fin_cases i <;> first | exact d.hc _ | exact bits_canonical _

theorem valid (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.before) (hq3 : p.b+3≤p.q) :
    ActiveRepairEarlyKeyOriginalValid.Valid (repair d) := by
  apply ActiveRepairEarlyKeyOriginalGeometry.geometry_valid (repair d) s (p.n*p.b) (p.n*p.q)
    p.before p.after offset (p.f*p.q) (rowBits d) rfl p.compactFits p.activeSize hfit
    (originals_value d) (originals_canonical d) hq3 rfl rfl rfl p.hnf p.hr
  · intro i
    fin_cases i
    · exact d.hv 7
    · exact d.hv 9
    · exact d.hv 10
    · change Counter.value (bits (p.n+1))=p.f
      rw [bits_value]
      exact p.hnf
  · intro i
    fin_cases i <;> first | exact d.hc _ | exact bits_canonical _
  · exact d.hv 8
  · exact d.hc 8

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersData
