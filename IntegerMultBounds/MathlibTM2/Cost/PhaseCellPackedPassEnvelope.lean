module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedKeyCost

/-! One resource language for the initial and recovery interior passes. The
same polynomial envelope bounds both numeric formats and actual tape controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

structure PackedHaloPassEnvelope (p l s t u target rhsExp a b V Z : ℕ) : Prop where
  positive : 1 ≤ Z
  parameter : 2^15*p ≤ Z
  stage : executionStagePrecision p l target rhsExp+1 ≤ Z
  precision : executionPrecision p l target rhsExp ≤ Z
  ringLog : l ≤ Z
  exponent : u ≤ Z
  width : executionWidth p l target rhsExp ≤ Z
  band : PhaseCellBand.width p u ≤ Z
  workspace : V ≤ Z
  familyWorkspace : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
    (executionWidth p l target rhsExp) t u ≤ Z
  candidates : ∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z
  keys : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
    ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z

/-- Geometry supplies every key-dependent dimension uniformly; no case split
on the numerical value of a candidate length is needed. -/
theorem PackedHaloPassEnvelope.of_bounds {p l s t u target rhsExp a b V Z : ℕ} [NeZero s]
    (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (htZ : t+2 ≤ Z)
    (hP : 2^15*p ≤ Z) (hstage : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z) (hband : PhaseCellBand.width p u ≤ Z) (hV : V ≤ Z)
    (hfamily : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z) :
    PackedHaloPassEnvelope p l s t u target rhsExp a b V Z := by
  have hs : 0 < s := NeZero.pos s
  have hlength : b-a ≤ s := (Nat.sub_le b a).trans hb
  have hphase := haloPhaseCount_scaled_le (t := t) hs a b hab
  have hvolume := Nat.mul_le_mul_left (2*(t-s)) hlength
  have hphases : haloPhaseCount s t a b ≤ t-s+2 := by nlinarith only [hphase,hvolume,hs]
  have hcandidates : ∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z := by
    intro L hL
    have h := haloLengthCandidates_uniform hst (PhaseCellBand.width p u) a b hL
    have hdiv := Nat.div_le_self s (t-s)
    omega
  refine ⟨by omega,hP,hstage,hq,hl,hu,hw,hband,hV,hfamily,hcandidates,?_⟩
  intro L hL x hx
  have hsub : (haloLengthKeys s t (PhaseCellBand.width p u) a b).Sublist
      (haloLengthCandidates s t (PhaseCellBand.width p u) a b) :=
    List.filter_sublist.trans (List.dedup_sublist _)
  have hLZ := hcandidates L (hsub.subset hL)
  have hgroup := haloLengthGroup_length_le s t (PhaseCellBand.width p u) a b L
  have hoffsets := haloPackedOffsets_length s t (PhaseCellBand.width p u) a b L
  simp only [packedHaloKeyDimensions,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end IntegerMultBounds.MathlibTM2.Cost
