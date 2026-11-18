module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignStream
public import IntegerMultBounds.MathlibTM2.Cover.FallbackItineraryMachine

/-! Compile one diagonalization program per invertible residue matrix for all its lifts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable {T Q A d : ℕ} {P U : Type}
local instance : Fact prime.Prime := ⟨prime_prime⟩
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ prime_prime.ne_zero⟩

theorem classDiagonalize_exec (body : P → Pr P T Q A U) (r : Fin 23 ↪ Fin T) (w H : ℕ)
    (C : Matrix (Fin d) (Fin d) (ZMod prime)) (unit : IsUnit C.det)
    (m : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1))))
    (residue : (LabelRing.res prime (w+1) (by omega)).mapMatrix m = C)
    (hm : prime^(w+1) < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H (prime^(w+1)))
    (one : S.R (r 20) = binSyms H (1 : ZMod (prime^(w+1))).val) (ticks : (S.R (r 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (r i) = []) :
    ∃ z F l suffix E a, z.user = v.user ∧ l ≤ d*(4*w+4+columnTime d prime w H)+1 ∧
      Exec body (itineraryProgram prime (classPivots C) r d) (mk v S) l (mk z F) ∧
      F.R (stageBank r d 15) = matrixWords A H (Matrix.diagonal a) ++ suffix ∧
      Elim (d*(d-1)) d E ∧ E*m = Matrix.diagonal a ∧ ∀ i, IsUnit (a i) := by
  apply diagonalize_exec body r prime w H prime_prime m (classPivots C) hm v S tail matrix modulus one ticks free
  apply (Itinerary.valid_map_iff (LabelRing.res prime (w+1) (by omega))
    (fun a ha => (LabelRing.isUnit_iff_res prime (w+1) (by omega) a).mpr ha.ne_zero) _ m d).mpr
  rw [residue]
  exact classPivots_valid C unit

end IntegerMultBounds.MathlibTM2.Cover.Fallback
