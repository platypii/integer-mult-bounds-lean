module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpInitializedData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineClearPrepared

/-! # Numerical release cost from the retained line interface -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Schoenhage.Schedule IntegerMultBounds.MathlibTM2.Node

def retainedReleaseCost (p q l Γ w t m M : ℕ) : ℕ :=
  2 * (3 * (w + q + topN w) + (M * (7 * m + 1) + m + 1) * w +
    4 * w + t * (p + l + Γ + 5)) + 45

/-- The retained setup's symbol volume is determined by scalar dimensions alone. -/
theorem LineData.clearPreparedCost {shared : Bool} {W s t α p q l Γ m w : ℕ} {S : Stacks 640 A}
    (h : LineData W s t α p q l Γ m w S shared) (hpq : p ≤ q) (hw : q + l + Γ + 5 ≤ w) :
    clearPreparedCost S.R = retainedReleaseCost p q l Γ w t m (chirpBlockCount t m) := by
  have hr : (readinessTargets.map fun k => (S.R k).length).sum = 3 * (w + q + topN w) := by
    simp only [readinessTargets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      h.ready.wn, h.ready.pn, h.ready.nn, h.outputState.cr_ready.wn,
      h.outputState.cr_ready.pn, h.outputState.cr_ready.nn, h.outputState.nr_ready.wn,
      h.outputState.nr_ready.pn, h.outputState.nr_ready.nn]
    omega
  have hG : (S.R (processor .ys)).length = chirpBlockCount t m * ((3 * m + 1) * w) := by
    rw [h.G]
    exact length_chirpBlockStream _ _ _ (fun _ _ => length_chirpEntryStream ..)
  have hK : (S.R (batch .srcY)).length = chirpBlockCount t m * ((4 * m) * w) := by
    rw [h.K]
    exact length_chirpBlockStream _ _ _ (fun _ _ => length_chirpEntryStream ..)
  have hE : (S.R (output.cr .ys)).length = m * w := by
    rw [h.outputState.factors, length_cstream, List.length_map, chirpOutputFactors_length]
  have hN : (S.R (output.nr .ys)).length = w := by
    rw [h.outputState.normalization]
    simp [csyms]
  have ht : (tableTargets.map fun k => (S.R k).length).sum =
      (chirpBlockCount t m * (7 * m + 1) + m + 1) * w := by
    simp only [tableTargets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hG, hK, hE, hN]
    ring
  have hd : ((List.ofFn output.dim).map fun k => (S.R k).length).sum =
      4 * w + t * (p + l + Γ + 5) := by
    simp only [List.map_ofFn, Function.comp_def, h.outdim]
    change ([l + 1, w - (l + 1), Γ, w - Γ, w, q - p, p + l + Γ + 5,
      w - (q - p) - (p + l + Γ + 5), t * (p + l + Γ + 5)] : List ℕ).sum = _
    simp only [List.sum_cons, List.sum_nil]
    omega
  simp only [LinePlacement.clearPreparedCost, prepareWrites, List.map_append, List.sum_append, hr, ht, hd,
    retainedReleaseCost]
  omega

/-- High caller/group ports never contribute to preparation release volume. -/
theorem clearPreparedCost_update_high (R : Regs 640 A) (k : Fin 640) (hk : 500 ≤ k.val)
    (xs : List (Fin (A + 4))) : clearPreparedCost (Function.update R k xs) = clearPreparedCost R := by
  have hm : (prepareWrites.map fun j => (Function.update R k xs j).length) =
      prepareWrites.map (fun j => (R j).length) := by
    apply List.map_congr_left
    intro j hj
    have hne : j ≠ k := by
      intro he
      have hjv := written_small j hj
      have hv := congrArg Fin.val he
      omega
    rw [Function.update_of_ne hne]
  unfold clearPreparedCost
  rw [hm]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
