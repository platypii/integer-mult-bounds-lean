module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicCopy
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.MathlibTM2.Fast.ResampASem

/-! # Construct the chirp cyclic source from the original line

Rotations and repetitions act on complete coefficient words. The resulting stream is
exactly `chirpExtended`; the raw source and all supplied counters are restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.ResampA

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem repeatStream_cstream (C A w : ℕ) (xs : List GaussianInt) :
    repeatStream C (cstream A w xs) = cstream A w (repeatStream C xs) := by
  induction C with
  | zero => simp
  | succ C ih => simp only [repeatStream_succ, cstream_append, ih]

/-- Exact symbol stream, including the original low-bit-first order inside every word. -/
theorem chirpCyclic_symbols {s : ℕ} (hs : 0 < s) (m A w : ℕ) (u : ZMod s → GaussianInt) :
    (repeatStream (chirpPeriods s m) (cstream A w ((chirpLine s u).drop (chirpOffset s m)) ++
      cstream A w ((chirpLine s u).take (chirpOffset s m)))).take ((s + 3 * m) * w) =
      cstream A w (chirpExtended s m u) := by
  rw [← cstream_append, ← List.rotate_eq_drop_append_take (by
    simpa using (chirpOffset_lt hs m).le)]
  rw [repeatStream_cstream, rsa_cstream_take, chirpExtended_eq_repeat hs]

/-- The cyclic source is built from the raw line; only the extension destination changes. -/
theorem chirpCyclic_exec {frontCount backCount count saved lengthR src front back acc expanded dst buf tmp : Fin T}
    (hreg : [frontCount, backCount, count, saved, lengthR, src, front, back, acc, expanded, dst, buf, tmp].Nodup)
    (s m w : ℕ) (hs : 0 < s) (u : ZMod s → GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (chirpLine s u))
    (hf : (S.R frontCount).length = chirpOffset s m * w)
    (hb : (S.R backCount).length = (s - chirpOffset s m) * w)
    (hc : (S.R count).length = chirpPeriods s m)
    (hN : (S.R lengthR).length = (s + 3 * m) * w)
    (hclean : ∀ k ∈ [saved, front, back, acc, expanded, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpPeriods s m * (8 * (s * w) + 9) + 10 * ((s + 3 * m) * w) + 10 * (s * w) + 38 ∧
      Exec body (cyclicCopy frontCount backCount count saved lengthR src front back acc expanded dst buf tmp)
        (mk v S) n (mk v' { S with R := Function.update S.R dst (cstream A w (chirpExtended s m u) ++ S.R dst) }) := by
  let xs := cstream A w ((chirpLine s u).take (chirpOffset s m))
  let ys := cstream A w ((chirpLine s u).drop (chirpOffset s m))
  have hxs : xs.length = chirpOffset s m * w := by
    simp only [xs, length_cstream, List.length_take, length_chirpLine,
      Nat.min_eq_left (chirpOffset_lt hs m).le]
  have hys : ys.length = (s - chirpOffset s m) * w := by
    simp only [ys, length_cstream, List.length_drop, length_chirpLine]
  have hsum : xs.length + ys.length = s * w := by
    rw [hxs, hys, ← Nat.add_mul, Nat.add_sub_of_le (chirpOffset_lt hs m).le]
  have hperiod : (repeatStream (chirpPeriods s m) (ys ++ xs)).take ((s + 3 * m) * w) =
      cstream A w (chirpExtended s m u) := chirpCyclic_symbols hs m A w u
  obtain ⟨v', n, hu, hn, he⟩ := cyclicCopy_exec (body := body) hreg xs ys ((s + 3 * m) * w)
    (chirpPeriods s m) v S (by simpa only [xs, ys, ← cstream_append, List.take_append_drop] using hsrc)
    (hf.trans hxs.symm) (hb.trans hys.symm) hc hN (by
      rw [hsum, ← Nat.mul_assoc]
      exact Nat.mul_le_mul_right w (chirpPeriods_cover hs m)) hclean
  exact ⟨v', n, hu, by simpa only [hsum] using hn, by simpa only [hperiod] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
