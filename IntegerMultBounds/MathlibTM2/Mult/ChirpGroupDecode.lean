module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupLoop
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardSelected

/-! # Decode the actual ordered group output, independently of its spectator suffix -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast

/-- An equal-width row can be recovered from the flattened batch before an arbitrary suffix. -/
theorem take_drop_flatten_map {E F : Type*} (f : E → List F) (us : List E) (w : ℕ)
    (hlen : ∀ u ∈ us, (f u).length = w) (suffix : List F) (i : ℕ) (hi : i < us.length) :
    ((((us.map f).flatten ++ suffix).drop (i * w)).take w) = f us[i] := by
  induction us generalizing i with
  | nil => simp at hi
  | cons u us ih =>
      have hu := hlen u (by simp)
      cases i with
      | zero =>
          simp only [List.map_cons, List.flatten_cons, List.append_assoc, Nat.zero_mul,
            List.drop_zero, List.getElem_cons_zero]
          rw [← hu]
          simp only [List.take_left]
      | succ i =>
          simp only [List.map_cons, List.flatten_cons, List.append_assoc,
            Nat.succ_mul, List.getElem_cons_succ]
          rw [Nat.add_comm (i * w) w, ← hu, List.drop_length_add_append]
          simpa only [hu] using ih (fun x hx => hlen x (by simp [hx])) i (by simpa using hi)

theorem groupLineInput_length (A s α p : ℕ) (u : ZMod s → GaussianInt) :
    (groupLineInput A s α p u).length =
      s * (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
        chirpForwardRingLog p α + chirpForwardGrowth p + 5) := by
  simp only [groupLineInput, length_cstream, length_chirpLine]

theorem groupLineOutput_length (A s t α p : ℕ) (hα : 1 ≤ α) (u : ZMod s → GaussianInt) :
    (groupLineOutput A s t α p u).length = t * (p + chirpForwardRingLog p α + chirpForwardGrowth p + 5) := by
  rw [groupLineOutput, length_cstream, chirpForwardOutput_length]
  · unfold chirpForwardWindow
    exact Nat.mul_pos (by omega) (by omega)
  · exact chirpForwardRingLog_good p α

/-- Read line i from the actual batch tape, then decode its fixed-width complex words. -/
noncomputable def readGroupLine (p wo t i : ℕ) (S : Stacks 640 A) : ZMod t → ℂ :=
  fun k => value p (decodeWord
    (((((S.R groupOutput).drop (i * (t * wo))).take (t * wo)).drop (k.val * wo)).take wo))

/-- The per-line resampling guarantee for a published batch tape. -/
def GroupOutputError (s t α p : ℕ) [NeZero s] [NeZero t] (us : List (ZMod s → GaussianInt)) (S : Stacks 640 A) : Prop :=
  ∀ i : Fin us.length,
    2 ^ p * ‖readGroupLine p (p + chirpForwardRingLog p α + chirpForwardGrowth p + 5) t i.val S -
      IntegerMultBounds.NLogN.resampA s t (α : ℝ)
        (fun j => value (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α)) (us[i] j))‖ ≤ 4

theorem readGroupLine_published (A s t α p : ℕ) (hα : 1 ≤ α)
    (us : List (ZMod s → GaussianInt)) (S : Stacks 640 A) (i : Fin us.length) :
    readGroupLine p (p + chirpForwardRingLog p α + chirpForwardGrowth p + 5) t i.val
      { S with R := (Function.update S.R groupOutput
        ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) } =
      chirpForwardDecoded A s t α p
        (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α))
        (chirpForwardRingLog p α) (chirpForwardGrowth p) (chirpForwardWindow p α) us[i] := by
  have hs := take_drop_flatten_map (groupLineOutput A s t α p) us
    (t * (p + chirpForwardRingLog p α + chirpForwardGrowth p + 5))
    (fun u _ => groupLineOutput_length A s t α p hα u) (S.R groupOutput) i.val i.isLt
  funext k
  dsimp only [readGroupLine]
  rw [Function.update_self, hs]
  simp only [groupLineOutput, chirpForwardDecoded, List.append_nil, Fin.getElem_fin]

/-- Every published line, decoded from its actual offset in the final tape, has error at most 4. -/
theorem publishedGroup_error {A s t : ℕ} [NeZero s] [NeZero t]
    (hA : 4 ≤ A) (hst : s < t) (α p : ℕ) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p)
    (us : List (ZMod s → GaussianInt))
    (hu : ∀ u ∈ us, ∀ j,
      ‖value (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α)) (u j)‖ ≤ 1)
    (S : Stacks 640 A) (i : Fin us.length) :
    2 ^ p * ‖readGroupLine p (p + chirpForwardRingLog p α + chirpForwardGrowth p + 5) t i.val
      { S with R := (Function.update S.R groupOutput
        ((us.map (groupLineOutput A s t α p)).flatten ++ S.R groupOutput)) } -
      IntegerMultBounds.NLogN.resampA s t (α : ℝ)
        (fun j => value (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α)) (us[i] j))‖ ≤ 4 := by
  rw [readGroupLine_published A s t α p hα us S i]
  exact chirpForwardSelected_error hA hst α p hα hαp us[i] (hu us[i] (List.getElem_mem i.isLt))

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
