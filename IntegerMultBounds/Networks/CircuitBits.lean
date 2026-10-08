import IntegerMultBounds.Networks.CircuitRouting
import Mathlib.Data.ZMod.Basic

/-! The bit motif as a finite scalar circuit over `ZMod 2`. Side wires are
ordered label pairs meeting in exactly one coordinate; the `h` central wires
are coordinate sums. There is no all-source-sum wire. The finite instruction
lists restore arbitrary dirty scratch and perform a true data-bank exchange.
Wire enumerations are explicit inputs; sparse wire counts and tape costs are
not established here. -/

namespace IntegerMultBounds.Networks.Circuit

/-- Ordered neighboring pairs for the bit motif. For three-element labels,
intersection size one already excludes equal labels. -/
abbrev BitPair {h n : ℕ} (L : Fin n → Finset (Fin h)) :=
  {p : Fin n × Fin n // (L p.1 ∩ L p.2).card = 1}

/-- Each side wire receives its source bit with coefficient one. -/
def bitCopy {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) : Fin a → Fin n → ZMod 2 :=
  fun p t => if (e p).val.2 = t then 1 else 0

/-- Each side wire is injected into its target with coefficient one. -/
def bitInject {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) : Fin n → Fin a → ZMod 2 :=
  fun s p => if (e p).val.1 = s then 1 else 0

/-- Exactly one central sum for each ground coordinate. -/
def bitGather {h n : ℕ} (L : Fin n → Finset (Fin h)) : Fin h → Fin n → ZMod 2 :=
  fun i t => if i ∈ L t then 1 else 0

/-- A target receives the central sums for its three coordinates. -/
def bitScatter {h n : ℕ} (L : Fin n → Finset (Fin h)) : Fin n → Fin h → ZMod 2 :=
  fun s i => if i ∈ L s then 1 else 0

theorem bit_central_coeff {h n : ℕ} (L : Fin n → Finset (Fin h)) (s t : Fin n) :
    (∑ i, bitScatter L s i * bitGather L i t) = ((L s ∩ L t).card : ZMod 2) := by
  have hh (i : Fin h) :
      bitScatter L s i * bitGather L i t =
        if i ∈ L s ∩ L t then (1 : ZMod 2) else 0 := by
    simp only [bitScatter, bitGather]
    split_ifs <;> simp_all
  simp_rw [hh]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i ∈ L s ∩ L t) = L s ∩ L t := by ext; simp
  rw [hf]
  simp

theorem bit_side_coeff {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) (s t : Fin n) :
    (∑ p, bitInject e s p * bitCopy e p t) =
      if (L s ∩ L t).card = 1 then 1 else 0 := by
  have term (p : Fin a) : bitInject e s p * bitCopy e p t =
      if (e p).val = (s, t) then 1 else 0 := by
    by_cases hs : (e p).val.1 = s <;> by_cases ht : (e p).val.2 = t <;>
      simp [bitInject, bitCopy, hs, ht, Prod.ext_iff]
  simp_rw [term]
  by_cases hst : (L s ∩ L t).card = 1
  · let q : BitPair L := ⟨(s, t), hst⟩
    have he (p : Fin a) : (e p).val = (s, t) ↔ p = e.symm q := by
      change (e p).val = q.val ↔ _
      rw [← Subtype.ext_iff, ← e.eq_symm_apply]
    simp [he, hst]
  · have he (p : Fin a) : (e p).val ≠ (s, t) := by
      intro hp
      apply hst
      have := (e p).property
      simpa only [hp] using this
    simp [he, hst]

/-- The natural parity coefficient proved in `Scalar` is the actual coefficient
of the side-plus-central circuit over the two-element field. -/
theorem bit_total_coeff {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) (s t : Fin n) :
    (∑ p, bitInject e s p * bitCopy e p t) +
      (∑ i, bitScatter L s i * bitGather L i t) = (bitCoefficient (L s) (L t) : ZMod 2) := by
  rw [bit_side_coeff, bit_central_coeff]
  simp only [bitCoefficient, ZMod.natCast_mod, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  exact add_comm _ _

/-- The finite bit-motif matrices reconstruct every source bank. -/
theorem bit_reconstruct {h n a : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X : Fin n → ZMod 2) :
    mv (bitInject e) (mv (bitCopy e) X) +
      mv (bitScatter L) (mv (bitGather L) X) = X := by
  apply reconstruct_of_coefficients
  intro s t
  rw [bit_total_coeff, bitCoefficient_eq _ _ (hcard s) (hcard t)]
  simp only [hinj.eq_iff, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- An actual finite dirty-scratch instruction list implements the bit shear,
restoring both scratch banks and every spectator register. -/
theorem bit_dirty_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin h → ZMod 2) (S : Fin s → ZMod 2) :
    run (dirty (bitCopy e) (bitGather L) (bitInject e) (bitScatter L))
      (banks X Y A C S) = banks X (Y + X) A C S := by
  exact dirty_run_shear _ _ _ _ (bit_reconstruct e hinj hcard) X Y A C S

/-- In characteristic two the signed exchange is a true swap, with arbitrary
original dirty scratch and spectators exactly restored. -/
theorem bit_exchange_run {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) (hinj : Function.Injective L)
    (hcard : ∀ i, (L i).card = 3) (X Y : Fin n → ZMod 2)
    (A : Fin a → ZMod 2) (C : Fin h → ZMod 2) (S : Fin s → ZMod 2) :
    run (signedExchangeProgram (bitCopy e) (bitGather L) (bitInject e) (bitScatter L))
      (banks X Y A C S) = banks Y X A C S := by
  rw [signedExchangeProgram_run _ _ _ _ (bit_reconstruct e hinj hcard)]
  have hneg : -Y = Y := by funext i; exact ZMod.neg_eq_self_mod_two (Y i)
  rw [hneg]

/-- This is the number of elementary scalar register updates, not grouped
multi-output gates, arithmetic operations on tapes, or a tape running time. -/
theorem bit_exchange_length {h n a s : ℕ} {L : Fin n → Finset (Fin h)}
    (e : Fin a ≃ BitPair L) :
    (signedExchangeProgram (s := s) (bitCopy e) (bitGather L)
      (bitInject e) (bitScatter L)).length = 3 * (4 * n + 2 * a + 2 * h) :=
  signedExchangeProgram_length _ _ _ _

end IntegerMultBounds.Networks.Circuit
