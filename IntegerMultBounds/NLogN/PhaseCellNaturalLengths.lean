module

public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups

/-! Every original phase-cell interior has one of four computable lengths:
two clipped endpoint lengths and two adjacent interior lengths. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem div_step_cases (n a b : ℕ) (hb : 0 < b) :
    (n+a)/b-n/b = a/b ∨ (n+a)/b-n/b = a/b+1 := by
  rw [Nat.add_div hb]
  split_ifs
  · right; simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  · left; simp only [Nat.add_zero, Nat.add_sub_cancel_left]

theorem phaseLower_step {s d phase : ℕ} (hd : 0 < d) (hp : 0 < phase) :
    phaseLower s d (phase+1)-phaseLower s d phase = s/d ∨
      phaseLower s d (phase+1)-phaseLower s d phase = s/d+1 := by
  have hsp : s ≤ 2*s*phase := by nlinarith only [hp]
  have he : 2*s*(phase+1) = 2*s*phase+2*s := by ring
  have hshift : 2*s*(phase+1)+2*d-1-s = (2*s*phase+2*d-1-s)+2*s := by
    rw [he]
    omega
  unfold phaseLower
  rw [hshift]
  simpa only [Nat.mul_div_mul_left s d (by decide : 0 < 2)] using
    div_step_cases (2*s*phase+2*d-1-s) (2*s) (2*d) (by omega)

theorem naturalLength_middle {s t phase : ℕ} (hst : s < t) (band : ℕ)
    (hp : 0 < phase) (hphase : phase < t-s) :
    naturalLength s t band phase = s/(t-s)-2*band ∨
      naturalLength s t band phase = (s/(t-s)+1)-2*band := by
  have hd : 0 < t-s := Nat.sub_pos_of_lt hst
  have hcap : phaseLower s (t-s) (phase+1) ≤ s := by
    apply (phaseLower_le hd).mpr
    have hh := Nat.mul_le_mul_left (2*s) (show phase+1 ≤ t-s by omega)
    nlinarith only [hh]
  have hlen : naturalLength s t band phase =
      (phaseLower s (t-s) (phase+1)-phaseLower s (t-s) phase)-2*band := by
    unfold naturalLength naturalStop naturalStart
    rw [min_eq_right hcap]
    omega
  rw [hlen]
  rcases phaseLower_step (s := s) hd hp with he | he <;> simp [he]

theorem naturalLength_le_uniform {s t : ℕ} (hst : s < t) (band phase : ℕ) :
    naturalLength s t band phase ≤ (s/(t-s)+1)-2*band := by
  have hd : 0 < t-s := Nat.sub_pos_of_lt hst
  have hstep : naturalLength s t band phase ≤
      (phaseLower s (t-s) (phase+1)-phaseLower s (t-s) phase)-2*band := by
    have hm := min_le_right s (phaseLower s (t-s) (phase+1))
    unfold naturalLength naturalStop naturalStart
    omega
  by_cases hp : phase = 0
  · subst phase
    have hzero : phaseLower s (t-s) 0 = 0 := by
      unfold phaseLower
      apply Nat.div_eq_of_lt
      omega
    have hdiv := Nat.div_add_mod s (t-s)
    have hmod := Nat.mod_lt s hd
    have hsquot : s < (t-s)*(s/(t-s)+1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hfirst : phaseLower s (t-s) 1 ≤ s/(t-s)+1 := by
      apply (phaseLower_le hd).mpr
      nlinarith only [hsquot]
    rw [hzero, Nat.sub_zero] at hstep
    exact hstep.trans (Nat.sub_le_sub_right hfirst (2*band))
  · rcases phaseLower_step (s := s) hd (by omega : 0 < phase) with he | he
    · rw [he] at hstep
      exact hstep.trans (Nat.sub_le_sub_right (by omega) (2*band))
    · simpa only [he] using hstep

def naturalLengthCandidates (s t band : ℕ) : List ℕ :=
  [naturalLength s t band 0, naturalLength s t band (t-s),
    s/(t-s)-2*band, (s/(t-s)+1)-2*band]

theorem naturalLengthCandidates_uniform {s t L : ℕ} (hst : s < t) (band : ℕ)
    (hL : L ∈ naturalLengthCandidates s t band) : L ≤ (s/(t-s)+1)-2*band := by
  simp only [naturalLengthCandidates, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact naturalLength_le_uniform hst band 0
  · exact naturalLength_le_uniform hst band (t-s)
  · exact Nat.sub_le_sub_right (by omega) (2*band)
  · exact le_rfl

theorem naturalLengthCandidates_le {s t L : ℕ} (hst : s < t) (band : ℕ)
    (hL : L ∈ naturalLengthCandidates s t band) : L ≤ s+1 :=
  (naturalLengthCandidates_uniform hst band hL).trans
    ((Nat.sub_le _ _).trans (Nat.add_le_add_right (Nat.div_le_self s (t-s)) 1))

theorem naturalLength_mem_candidates {s t phase : ℕ} (hst : s < t) (band : ℕ)
    (hphase : phase ≤ t-s) : naturalLength s t band phase ∈ naturalLengthCandidates s t band := by
  by_cases hzero : phase = 0
  · simp [naturalLengthCandidates, hzero]
  by_cases hlast : phase = t-s
  · simp [naturalLengthCandidates, hlast]
  rcases naturalLength_middle (phase := phase) hst band (by omega) (by omega) with he | he <;>
    simp [naturalLengthCandidates, he]

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
