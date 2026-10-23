module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputValue
public import IntegerMultBounds.MathlibTM2.Fast.PointStage

/-! # Exact numerator shifts on the chirp output tape

Specialize the existing word-preserving shift program to Gaussian integer streams.
Only the source stream changes; reusable shift counts and all scratch are restored.
Signed decoding additionally requires the shifted numerators to fit their words.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.ChirpSt

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Execute exact numerator multiplication by a power of two, retaining every other tape. -/
theorem chirpScale_exec {src buf shift rest savedShift savedRest : Fin T}
    (hreg : [src, buf, shift, rest, savedShift, savedRest].Nodup)
    (w d : ℕ) (hw : 1 ≤ w) (hd : d ≤ w) (xs : List GaussianInt)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = cstream A w xs)
    (hshift : (S.R shift).length = d) (hrest : (S.R rest).length = w - d)
    (hbuf : S.R buf = []) (hsavedShift : S.R savedShift = []) (hsavedRest : S.R savedRest = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (shiftInto src buf src shift rest savedShift savedRest (pairSym A false false))
        (mk v S) (xs.length * (6 * w + 4 * d + 14) + 4)
        (mk v' { S with R := (Function.update S.R src
          (cstream A w (xs.map fun x => (2 : GaussianInt) ^ d * x))) }) := by
  have hne : src ≠ buf := by
    intro h
    exact (List.nodup_cons.mp hreg).1 (by simp [h])
  obtain ⟨v', R', hu, hscan, he, hout, hsrc', hoff⟩ := shiftInto_exec (body := body)
    src buf src shift rest savedShift savedRest hreg hne hw hd (xs.map (red w)) v S
    (by simpa only [cst_cstream_eq_red] using hsrc) hshift hrest hsavedShift hsavedRest hbuf
  have hwords : ((xs.map (red w)).map fun z =>
      ((2 ^ d : ZMod (2 ^ w)) * z.1, (2 ^ d : ZMod (2 ^ w)) * z.2)).flatMap (coeffSyms A w) =
      cstream A w (xs.map fun x => (2 : GaussianInt) ^ d * x) := by
    rw [cst_cstream_eq_red, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact (cst_red_two_pow_mul w d x).symm
  rw [hwords, ite_eq_left rfl, List.append_nil] at hout
  refine ⟨v', hu, he.cast (by simp) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = src
  · subst k
    simpa only [Function.update_self] using hout
  · simpa only [Function.update_of_ne hk] using hoff k hk hk

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
