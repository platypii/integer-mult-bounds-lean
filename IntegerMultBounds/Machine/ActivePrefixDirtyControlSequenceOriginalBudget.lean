import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalRun
import IntegerMultBounds.Machine.ActivePrefixDirtyControlHeadersBudget
import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceBudget

/-! The complete original-input later algorithm pays all three physical
header producers and cleanups while retaining the certified width exponent. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalBudget
open CompactGadgetReservationShape
open ActivePrefixLayoutShapes
open ActivePrefixEarlySequenceOriginalInputs (Inputs)
open ActivePrefixDirtyControlSequenceOriginalInputs (layout geometry)
open ActivePrefixDirtyControlSequenceOriginalRun
open Networks
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def overhead := 3*(ActivePrefixDirtyControlHeadersBudget.constant+ActivePrefixDirtyControlHeadersBudget.cleanupConstant)

theorem headers_bound (hfit : offset+p.f*p.q≤p.after) (d : Inputs s p offset rows) :
    headerCost d≤overhead*(rows*s.recordWidth) := by
  have hp : 0<s.payload := by have := d.hrecord; omega
  have hV : 0<rows*s.recordWidth := by have hr := d.hr; unfold Shape.recordWidth; positivity
  have ho := ActivePrefixLayoutHeadersGeometry.originals_bound s p offset rows .compactAfter hfit d.hr d.hrecord
  have hc (k : ActivePrefixDirtyControlHeadersData.Kind) := ActivePrefixDirtyControlHeadersBudget.cost_bound k
    (layout d) (rows*s.recordWidth) hV hp ho
    (ActivePrefixLayoutHeadersGeometry.suffix_bound s p offset rows (ActivePrefixDirtyControlHeadersData.mode k) d.hr)
  have he (k : ActivePrefixDirtyControlHeadersData.Kind) := ActivePrefixDirtyControlHeadersBudget.cleanup_bound k
    (layout d) (rows*s.recordWidth) hV ho
    (ActivePrefixLayoutHeadersGeometry.suffix_bound s p offset rows (ActivePrefixDirtyControlHeadersData.mode k) d.hr)
  have h₀ := hc .target
  have h₁ := hc .compact
  have h₂ := hc .source
  have h₃ := he .target
  have h₄ := he .compact
  have h₅ := he .source
  unfold headerCost overhead
  nlinarith only [h₀,h₁,h₂,h₃,h₄,h₅]

theorem uniform_bound : ∃ C : ℝ, 0<C ∧ ∀ (s : Shape) (p : Parameters s) (offset rows : ℕ)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b) (d : Inputs s p offset rows),
    (cost hfit hn hb d : ℝ)≤C*(rows*s.recordWidth : ℕ)*
      ((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := ActivePrefixDirtyControlSequenceBudget.uniform_bound
  refine ⟨C+overhead+6,by positivity,?_⟩
  intro s p offset rows hfit hn hb d
  have hi := hbound s (geometry hfit hn hb d)
  have hh := headers_bound hfit d
  have hV : (1 : ℝ)≤(rows*s.recordWidth : ℕ) := by
    have hp : 0<s.payload := by have := d.hrecord; omega
    have hr := d.hr
    have h : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
    exact_mod_cast h
  have he : (1 : ℝ)≤((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau :=
    Real.one_le_rpow (by exact_mod_cast le_max_left 1 (p.n*p.b))
      Shared50RecursiveBudgetBound.exponent_range.1.le
  have hm := mul_le_mul_of_nonneg_left he (show (0 : ℝ)≤(rows*s.recordWidth : ℕ) by positivity)
  have hrest := mul_le_mul_of_nonneg_left hm (show (0 : ℝ)≤(overhead : ℝ)+6 by positivity)
  change ((headerCost d+ActivePrefixDirtyControlSequenceRun.cost s (geometry hfit hn hb d)+6 : ℕ) : ℝ)≤_
  have hh' : (headerCost d : ℝ)≤(overhead : ℝ)*(rows*s.recordWidth : ℕ) := by exact_mod_cast hh
  change (ActivePrefixDirtyControlSequenceRun.cost s (geometry hfit hn hb d) : ℝ)≤
    C*(rows*s.recordWidth : ℕ)*((max 1 (p.n*p.b) : ℕ) : ℝ)^IntegerMultBounds.Parameters.tau at hi
  push_cast at hi hV hrest hh' ⊢
  nlinarith only [hi,hh',hV,hrest]

end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalBudget
