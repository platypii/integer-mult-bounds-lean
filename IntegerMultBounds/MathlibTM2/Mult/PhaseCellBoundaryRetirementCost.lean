module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetirePublishedBoundary
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundaryCount

/-! Uniform dimension-only bounds for packed-table and published-prefix retirement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem clipUnaryCost_le (N x : ℕ) : clipUnaryCost N x ≤ 14*N+6*x+20 := by
  dsimp [clipUnaryCost]
  omega

theorem clippedBandControlsCost_le (n W N : ℕ) :
    clippedBandControlsCost n W N ≤ 18*n+14*W+14*N+47 := by
  have hh := clipUnaryCost_le N (n+W+1)
  dsimp [clippedBandControlsCost,bandIntervalEndpointsCost]
  omega

theorem retirePackedBandColumnCost_le (n W N w : ℕ) :
    retirePackedBandColumnCost n W N w ≤ 20*n+14*N+36*W+12*(2*W+1)*w+75 := by
  have hclip := clippedBandControlsCost_le n W N
  have hc : min N (n+W+1)-(n-W) ≤ 2*W+1 := by omega
  have hcw := Nat.mul_le_mul_right w hc
  have hn := Nat.sub_le n W
  dsimp only [retirePackedBandColumnCost]
  nlinarith only [hclip,hc,hcw,hn]

theorem retirePackedBandStepCost_le {n W N w : ℕ} (hn : n ≤ N) :
    retirePackedBandStepCost n W N w ≤ 40*N+36*W+12*(2*W+1)*w+81 := by
  have hh := retirePackedBandColumnCost_le n W N w
  dsimp only [retirePackedBandStepCost]
  omega

def retirePackedBandTableCostBound (N W w : ℕ) : ℕ :=
  N*(40*N+36*W+12*(2*W+1)*w+88)+6

theorem retirePackedBandTableCost_le (N W w : ℕ) :
    retirePackedBandTableCost N W w ≤ retirePackedBandTableCostBound N W w := by
  have hsum : (Finset.range N).sum (fun j => retirePackedBandStepCost (N-(j+1)) W N w+3) ≤
      N*(40*N+36*W+12*(2*W+1)*w+84) := by
    calc
      _ ≤ (Finset.range N).sum (fun _ => 40*N+36*W+12*(2*W+1)*w+84) := by
        apply Finset.sum_le_sum
        intro j _
        have hh := retirePackedBandStepCost_le (W := W) (w := w) (Nat.sub_le N (j+1))
        omega
      _ = _ := by simp
  dsimp only [retirePackedBandTableCost,retirePackedBandTableCostBound]
  nlinarith only [hsum]

def retirePublishedBoundaryCostBound (s N W w : ℕ) : ℕ :=
  retirePackedBandTableCostBound N W w+18*s*w+9*s+18

theorem retirePublishedBoundaryCost_le (s N W w : ℕ) :
    retirePublishedBoundaryCost s N W w ≤ retirePublishedBoundaryCostBound s N W w := by
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (retirePackedBandTableCost_le N W w) _) _) _

theorem retirePublishedBoundaryCostBound_mono {N M : ℕ} (hN : N ≤ M) (s W w : ℕ) :
    retirePublishedBoundaryCostBound s N W w ≤ retirePublishedBoundaryCostBound s M W w := by
  have hf : 40*N+36*W+12*(2*W+1)*w+88 ≤ 40*M+36*W+12*(2*W+1)*w+88 := by omega
  have hh := Nat.mul_le_mul hN hf
  dsimp only [retirePublishedBoundaryCostBound,retirePackedBandTableCostBound]
  omega

def haloBoundaryRetirementCostBound (s t band a b w : ℕ) : ℕ :=
  retirePublishedBoundaryCostBound s
    (haloBoundaryCountBound s t band a b) (12*band+1) w

theorem haloBoundary_retirement_cost_le {s t : ℕ} [NeZero s] (hst : s < t) (band a b w : ℕ) :
    retirePublishedBoundaryCostBound s
      (haloBoundary s t band a b).card (12*band+1) w ≤
      haloBoundaryRetirementCostBound s t band a b w :=
  retirePublishedBoundaryCostBound_mono
    (haloBoundary_card_bound hst band a b) s (12*band+1) w

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem retirePublishedBoundary_exec_bounded {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (xs ys tail : List (Fin (A+4))) (hxs : xs.length = s*w) (hys : ys.length = s*w)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hs : (S.R 121).length = s) (hW : (S.R 190).length = W)
    (hN : (S.R 116).length = B.card) (hw : (S.R 160).length = w)
    (hsource : S.R 132 = xs++(bandTableWords A w B W columns 0++ys++tail))
    (hfresh : ∀ i ∈ ([184,217,152,151,131,134,135,136,137,138] : List (Fin 224)), S.R i = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ retirePublishedBoundaryCostBound s B.card W w ∧
      Exec body retirePublishedBoundary (mk v S) m
        (mk v' {S with R := Function.update S.R 132 (xs++tail)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := retirePublishedBoundary_exec (body := body) B W w columns hlen xs ys tail hxs hys
    v S hs hW hN hw hsource hfresh
  exact ⟨v',m,hu,hm.trans (retirePublishedBoundaryCost_le s B.card W w),he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
