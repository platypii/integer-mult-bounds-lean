module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupDecode
public import IntegerMultBounds.MathlibTM2.Mult.ChirpReleaseCost
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupControls

/-! # Numerical lengths and per-line costs of a forward group -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast

/-- Equal-width rows contribute exactly their count times the width to a batch. -/
theorem length_flatten_map_of_length {E F : Type*} (f : E → List F) (us : List E) (w : ℕ)
    (hlen : ∀ u ∈ us, (f u).length = w) : (us.map f).flatten.length = us.length * w := by
  induction us with
  | nil => simp
  | cons u us ih =>
      rw [List.map_cons, List.flatten_cons, List.length_append, hlen u (by simp),
        ih (fun x hx => hlen x (by simp [hx])), List.length_cons]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem groupInputBatch_length (A s α p : ℕ) (us : List (ZMod s → GaussianInt)) :
    (us.map (groupLineInput A s α p)).flatten.length =
      us.length * (s * (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
        chirpForwardRingLog p α + chirpForwardGrowth p + 5)) :=
  length_flatten_map_of_length _ us _ (fun u _ => groupLineInput_length A s α p u)

theorem groupOutputBatch_length (A s t α p : ℕ) (hα : 1 ≤ α) (us : List (ZMod s → GaussianInt)) :
    (us.map (groupLineOutput A s t α p)).flatten.length =
      us.length * (t * (p + chirpForwardRingLog p α + chirpForwardGrowth p + 5)) :=
  length_flatten_map_of_length _ us _ (fun u _ => groupLineOutput_length A s t α p hα u)

/-- The cost bound of a collected line depends only on the selected scalar dimensions. -/
def groupLineBound (s t α p : ℕ) (shared : Bool := false) : ℕ :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let wo := p + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  chirpRawCorrelationModeCost shared W w W w s t q l m w +
    chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t +
    16 * (s * w) + 2 * (t * wo) + 18

theorem groupLineCost_eq {shared : Bool} (A s t α p : ℕ) (hα : 1 ≤ α) (u : ZMod s → GaussianInt) :
    groupLineCost A s t α p u shared = groupLineBound s t α p shared := by
  simp only [groupLineCost, groupLineInput_length, groupLineOutput_length A s t α p hα,
    groupLineBound]

theorem groupLineCost_sum {shared : Bool} (A s t α p : ℕ) (hα : 1 ≤ α) (us : List (ZMod s → GaussianInt)) :
    (us.map (fun u => groupLineCost A s t α p u shared)).sum = us.length * groupLineBound s t α p shared := by
  induction us with
  | nil => simp
  | cons u us ih =>
      rw [List.map_cons, List.sum_cons, groupLineCost_eq (shared := shared) A s t α p hα u, ih, List.length_cons]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Numerical loop and archive overhead after shared setup. -/
def groupRunBound (s t α p N : ℕ) (shared : Bool := false) : ℕ :=
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let wo := p + l + Γ + 5
  N * groupLineBound s t α p shared + 5 * N + 2 * (N * (s * w)) + 2 * (N * (t * wo)) + 8

theorem groupRunCost_eq {shared : Bool} (A s t α p : ℕ) (hα : 1 ≤ α) (us : List (ZMod s → GaussianInt)) :
    (us.map (fun u => groupLineCost A s t α p u shared)).sum + 5 * us.length +
      2 * (us.map (groupLineInput A s α p)).flatten.length +
      2 * (us.map (groupLineOutput A s t α p)).flatten.length + 8 =
      groupRunBound s t α p us.length shared := by
  rw [groupLineCost_sum (shared := shared) A s t α p hα us, groupInputBatch_length A s α p us,
    groupOutputBatch_length A s t α p hα us]
  rfl

/-- Complete numerical group cost, with setup and release paid once. -/
def selectedGroupCost (s t α p N : ℕ) : ℕ :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let M := chirpBlockCount t m
  let B := chirpForwardCallerBase s t p
  let W := chirpForwardTableWord q B
  (initializeCost W (Nat.size B) p q l Γ w t m M +
    (2 * IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC W w +
      (6 * (s * w) + 11 * W + 7)) +
    (controlsSetupCost W w s t m M + groupRunBound s t α p N true)) +
    (controlsReleaseCost s t m w M +
      ((2 * (s * w) + 2) + (retainedReleaseCost p q l Γ w t m M + (218 * W + 12 * w + 243))))

/-- All costs outside this unit term are paid once for the entire group. -/
def selectedGroupUnitCost (s t α p : ℕ) : ℕ :=
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  groupLineBound s t α p true + 5 +
    2 * (s * (q + l + Γ + 5)) + 2 * (t * (p + l + Γ + 5))

/-- Exact separation of shared setup/release from repeated line work. -/
theorem selectedGroupCost_affine (s t α p N : ℕ) :
    selectedGroupCost s t α p N =
      selectedGroupCost s t α p 0 + N * selectedGroupUnitCost s t α p := by
  unfold selectedGroupCost groupRunBound selectedGroupUnitCost
  ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
