import IntegerMultBounds.Machine.PackedInverse
import IntegerMultBounds.Compact.PackedArithValue
import IntegerMultBounds.Compact.Permutations

/-! The inverse packed program on tapes computes the inverse of the packed
permutation: applying `packedEarly` to the integers of its recovered words
returns the integers of its input words, so by injectivity the recovered
address is the permutation's preimage. -/

namespace IntegerMultBounds.Compact.PowerTwo

open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine.PackedInverse
open IntegerMultBounds.Machine.ColumnTransducer (addRule_value subRule_value)
open Radix

theorem emod_cancel_add (x y M : ℤ) : ((x + y) % M - y) % M = x % M := by
  rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod, add_sub_cancel_right]

theorem emod_cancel_sub (x y M : ℤ) : ((x - y) % M + y) % M = x % M := by
  rw [Int.add_emod, Int.emod_emod, ← Int.add_emod, sub_add_cancel]

theorem value_lt_blocks (X : List Bool) (n w : ℕ) (hX : X.length = n * w) :
    (value X : ℤ) < ((2 : ℤ) ^ w) ^ n := by
  rw [pow_blocks, ← hX]
  exact_mod_cast Counter.value_lt X

section Lines

variable (q b : ℕ) (hb : 1 ≤ b) (hbq : b + 1 ≤ q) (V2 W2 Z : List Bool)
  (hV : V2.length = Z.length * q) (hW : W2.length = Z.length * b)

include hV hW in
/-- The forward integer program on the recovered words returns the inputs. -/
theorem inverse_value :
    packedEarly ((2 : ℤ) ^ q) ((2 : ℤ) ^ b) (Z.map ctrl) (value (v q b hb hbq V2 W2 Z))
      (value (w q b hb hbq V2 W2 Z)) = ((value V2 : ℤ), (value W2 : ℤ)) := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths q b hb hbq V2 W2 Z hV hW
  have hn : (Z.map ctrl).length = Z.length := by simp
  set M : ℤ := ((2 : ℤ) ^ q) ^ Z.length with hM
  set N : ℤ := ((2 : ℤ) ^ b) ^ Z.length with hN
  -- the recovered words as residues
  have hw1 : (value (w1 q b hb hbq V2 W2 Z) : ℤ) =
      ((value W2 : ℤ) + pack ((2 : ℤ) ^ b) (List.zipWith (fun v z => (v % 2 + z) % 2)
        (digits ((2 : ℤ) ^ q) Z.length (value V2)) (Z.map ctrl))) % N := by
    rw [w1, addMod_value _ _ (by rw [hW, l1]), off1, toggle_value q b hb hbq Z V2 hV, hW, hN, pow_blocks]
  have ht : (value (t q b hb hbq V2 W2 Z) : ℤ) =
      ((value V2 : ℤ) - pack ((2 : ℤ) ^ q) (Z.map ctrl)) % M := by
    rw [t, subRule_value _ _ (by rw [hV, l3]), off2a, controls_value q b hb hbq Z W2 (by
      rw [hW]; exact Nat.le_mul_of_pos_right _ hb), hV, hM, pow_blocks]
  have hv1 : (value (v1 q b hb hbq V2 W2 Z) : ℤ) =
      ((value (t q b hb hbq V2 W2 Z) : ℤ) + pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => 2 * z * w)
        (Z.map ctrl) (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V2 W2 Z))))) % M := by
    rw [v1, addMod_value _ _ (by rw [l4, l5]), off2b, maskShift_value q b hb hbq Z _ l2, l4, hM, pow_blocks]
  have hwd : (value (w q b hb hbq V2 W2 Z) : ℤ) =
      ((value (w1 q b hb hbq V2 W2 Z) : ℤ) - pack ((2 : ℤ) ^ b)
        ((digits ((2 : ℤ) ^ q) Z.length (value (v1 q b hb hbq V2 W2 Z))).map (· % 2))) % N := by
    rw [w, subRule_value _ _ (by rw [l2, l7]), off3, parity_value q b hb hbq Z _ l6, l2, hN, pow_blocks]
  have hvd : (value (v q b hb hbq V2 W2 Z) : ℤ) =
      ((value (v1 q b hb hbq V2 W2 Z) : ℤ) - pack ((2 : ℤ) ^ q) (List.zipWith (fun z w => 2 * z * w)
        (Z.map ctrl) (digits ((2 : ℤ) ^ b) Z.length (value (w q b hb hbq V2 W2 Z))))) % M := by
    rw [v, subRule_value _ _ (by rw [l6, l9]), off4, maskShift_value q b hb hbq Z _ l8, l6, hM, pow_blocks]
  -- bounds
  have bV2 : (value V2 : ℤ) < M := value_lt_blocks V2 Z.length q hV
  have bW2 : (value W2 : ℤ) < N := value_lt_blocks W2 Z.length b hW
  have bv1 : (value (v1 q b hb hbq V2 W2 Z) : ℤ) < M := value_lt_blocks _ Z.length q l6
  have bw1 : (value (w1 q b hb hbq V2 W2 Z) : ℤ) < N := value_lt_blocks _ Z.length b l2
  -- the forward lines on the recovered words
  have f1 : ((value (v q b hb hbq V2 W2 Z) : ℤ) + pack ((2 : ℤ) ^ q)
      (List.zipWith (fun z w => 2 * z * w) (Z.map ctrl)
        (digits ((2 : ℤ) ^ b) Z.length (value (w q b hb hbq V2 W2 Z))))) % M =
      value (v1 q b hb hbq V2 W2 Z) := by
    rw [hvd, emod_cancel_sub, Int.emod_eq_of_lt (by positivity) bv1]
  have f2 : ((value (w q b hb hbq V2 W2 Z) : ℤ) + pack ((2 : ℤ) ^ b)
      ((digits ((2 : ℤ) ^ q) Z.length (value (v1 q b hb hbq V2 W2 Z))).map (· % 2))) % N =
      value (w1 q b hb hbq V2 W2 Z) := by
    rw [hwd, emod_cancel_sub, Int.emod_eq_of_lt (by positivity) bw1]
  have f3 : ((value (v1 q b hb hbq V2 W2 Z) : ℤ) + pack ((2 : ℤ) ^ q)
      (List.zipWith (fun z w => z * (1 - 2 * w)) (Z.map ctrl)
        (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V2 W2 Z))))) % M = value V2 := by
    have hzip : ∀ (C D : List ℤ), List.zipWith (fun z w => z * (1 - 2 * w)) C D =
        List.zipWith (fun x y => x - y) C (List.zipWith (fun z w => 2 * z * w) C D) := by
      intro C
      induction C with
      | nil => intro D; simp
      | cons c C ih =>
        intro D
        cases D with
        | nil => simp
        | cons d D => simp only [List.zipWith_cons_cons, ih]; congr 1; ring
    have hd : (digits ((2 : ℤ) ^ b) Z.length (value (w1 q b hb hbq V2 W2 Z))).length = Z.length :=
      digits_length _ _ _
    have key : ∀ x p y : ℤ, x - p + (y + (p - y)) = x := by intros; ring
    rw [hzip, pack_sub ((2 : ℤ) ^ q) (Z.map ctrl) _ (by rw [hn, List.length_zipWith, hn, hd, min_self]),
      hv1, ht, Int.emod_add_emod, add_assoc, Int.emod_add_emod, key,
      Int.emod_eq_of_lt (by positivity) bV2]
  have f4 : ((value (w1 q b hb hbq V2 W2 Z) : ℤ) - pack ((2 : ℤ) ^ b)
      (List.zipWith (fun v z => (v % 2 + z) % 2) (digits ((2 : ℤ) ^ q) Z.length (value V2))
        (Z.map ctrl))) % N = value W2 := by
    rw [hw1, emod_cancel_add, Int.emod_eq_of_lt (by positivity) bW2]
  simp only [packedEarly, hn]
  rw [f1, f2, f3, f4]

include hV hW in
/-- The recovered address is the packed permutation's preimage. -/
theorem inverse_perm (hQ : 0 < (2 : ℤ) ^ q) (hB : 0 < (2 : ℤ) ^ b) :
    (packedEarlyPerm ((2 : ℤ) ^ q) ((2 : ℤ) ^ b) hQ hB (Z.map ctrl)).symm
      (⟨(value V2 : ℤ), by positivity, by
          rw [List.length_map]; exact value_lt_blocks V2 Z.length q hV⟩,
       ⟨(value W2 : ℤ), by positivity, by
          rw [List.length_map]; exact value_lt_blocks W2 Z.length b hW⟩) =
      (⟨(value (v q b hb hbq V2 W2 Z) : ℤ), by positivity, by
          rw [List.length_map]
          exact value_lt_blocks _ Z.length q (lengths q b hb hbq V2 W2 Z hV hW).2.2.2.2.2.2.2.2.2⟩,
       ⟨(value (w q b hb hbq V2 W2 Z) : ℤ), by positivity, by
          rw [List.length_map]
          exact value_lt_blocks _ Z.length b (lengths q b hb hbq V2 W2 Z hV hW).2.2.2.2.2.2.2.1⟩) := by
  rw [Equiv.symm_apply_eq]
  have h := packedEarlyPerm_agrees ((2 : ℤ) ^ q) ((2 : ℤ) ^ b) hQ hB (Z.map ctrl)
    (⟨(value (v q b hb hbq V2 W2 Z) : ℤ), by positivity, by
        rw [List.length_map]
        exact value_lt_blocks _ Z.length q (lengths q b hb hbq V2 W2 Z hV hW).2.2.2.2.2.2.2.2.2⟩,
     ⟨(value (w q b hb hbq V2 W2 Z) : ℤ), by positivity, by
        rw [List.length_map]
        exact value_lt_blocks _ Z.length b (lengths q b hb hbq V2 W2 Z hV hW).2.2.2.2.2.2.2.1⟩)
  simp only at h
  rw [inverse_value q b hb hbq V2 W2 Z hV hW] at h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst h).symm
  · exact Subtype.ext (congrArg Prod.snd h).symm

end Lines

end IntegerMultBounds.Compact.PowerTwo
