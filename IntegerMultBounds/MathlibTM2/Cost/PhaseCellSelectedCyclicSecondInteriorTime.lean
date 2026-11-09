module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicSecondInteriorSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicSecondInteriorSharedSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock
import Mathlib.Tactic.Linarith

/-! Selected complete time allowance for the two actual second interiors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFittingCyclicSecondInterior_time_le (cl cw cr cV : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      let s := Sizes.s n i
      let t := Sizes.t n i
      let p := Sizes.p n
      ∀ width band depth L replicas : ℕ, 0 < width → width ≤ s →
      depth*band ≤ width → 1 ≤ band → s/(t-s)+1 ≤ width → p^2+band^2 ≤ width →
      ∀ H K J M : ℕ → ReplicaHaloProblem s,
      (∀ k ∈ coreGatherIndices s width (depth*band) L,
        (H k).p = p ∧ (H k).t = t ∧ (H k).band = band ∧
        (H k).origin = coreStart width k-depth*band ∧
        (H k).span = min L (s-(coreStart width k-depth*band)) ∧
        (K k).p = p ∧ (K k).t = t ∧ (K k).band = band ∧
        (K k).span = L-min L (s-(coreStart width k-depth*band))) →
      (∀ k ∈ coreGatherIndices s width (depth*band) L,
        (H k).SameLayout (J k) ∧ (K k).SameLayout (M k)) →
      (∀ k ∈ coreGatherIndices s width (depth*band) L, ∀ R ∈ [H k,K k],
        R.Fs.length = replicas ∧ R.u ≤ R.p ∧ R.l ≤ cl*R.p ∧ R.wordWidth ≤ cw*R.p ∧
        2^R.l ≤ cr*R.p ∧ R.metadataWidth ≤ cV*R.p ∧ R.l = haloInverseRingLog s R.t) →
      let jobs := coreGatherIndices s width (depth*band) L
      ((jobs.map (fun k => (H k).interiorTimeBudget (J k).target (J k).rhsExp+
        (K k).interiorTimeBudget (M k).target (M k).rhsExp)).sum : ℝ) ≤
      (Sizes.T n : ℝ)+680*F*replicas*((s+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hfast⟩ := computedFittingCyclicSecondInteriorSchedule_fast_le cl cw cr cV
  refine ⟨F,hF,?_⟩
  filter_upwards [selectedCyclicSecondInteriorSharedSchedule_volume_le cl cw cr cV 1] with n hs
  intro h i _
  dsimp only
  intro width band depth L replicas hw hwidth hguard hband hcell hprepare H K J M hgeom hlayout hparams
  let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
  have hcount : jobs.length ≤ 2*Sizes.t n i := by
    have hc := coreGatherIndices_length_le (Sizes.s n i) width (depth*band) L hw
    have hh := h.good.lt i
    dsimp only [jobs]
    omega
  have hshared := hs i jobs H K J M hcount hlayout (by
    intro k hk R hR
    obtain ⟨hpH,htH,_,_,_,hpK,htK,_,_⟩ := hgeom k hk
    obtain ⟨_,hu,hl,hw,hr,hV,_⟩ := hparams k hk R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact ⟨hpH,htH,hu,hl,hw,hr,hV⟩
    · exact ⟨hpK,htK,hu,hl,hw,hr,hV⟩)
  simp only [one_mul] at hshared
  have hn := hfast (h.good.lt i) (selectedAxis_gap_le_source h i) (Sizes.p n)
    width band depth L replicas hw hwidth hguard hband hcell hprepare H K J M hgeom hlayout (by
      intro k hk R hR
      obtain ⟨hcount,_,hl,hw,hr,hV,hring⟩ := hparams k hk R hR
      exact ⟨hcount,hl,hw,hr,hV,hring⟩)
  have hr := (Nat.cast_le (α := ℝ)).mpr hshared
  dsimp only [jobs] at hr
  exact hn.trans (add_le_add hr (le_refl _))

end IntegerMultBounds.MathlibTM2.Cost
