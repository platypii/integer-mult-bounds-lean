module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlaneData

/-! Actual numerical coefficient streams supply the packed router's plane views. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

/-- A rectangular paired word supplies both planes. The array views are derived
from the word, not supplied as certificates by the numerical caller. -/
theorem pairedWords_replica_view {A N K W : ℕ} (xs : List (Fin (A+4)))
    (hlen : xs.length = N*(K*W))
    (hpair : List.zipWith (pairSym A) (xs.map pairRe) (xs.map pairIm) = xs) :
    ∃ r i : Fin N → Fin K → Fin W → Bool,
      replicaKeyWords (fun n k b => pairSym A (r n k b) (i n k b)) = xs := by
  obtain ⟨r,hr⟩ := replicaKeyWords_of_length (xs.map pairRe) (by simpa using hlen)
  obtain ⟨i,hi⟩ := replicaKeyWords_of_length (xs.map pairIm) (by simpa using hlen)
  refine ⟨r,i,?_⟩
  rw [←replicaKeyWords_zipWith,hr,hi]
  exact hpair

/-- The numerical batch's key-major coefficient word is directly routable,
including negative coefficients and values outside signed decoding bounds. -/
theorem cstream_keyReplica_view {A N K W : ℕ} (hA : 4 ≤ A)
    (w : ℕ) (xs : List GaussianInt) (hlen : xs.length*w = K*(N*W)) :
    ∃ r i : Fin N → Fin K → Fin W → Bool,
      keyReplicaWords (fun n k b => pairSym A (r n k b) (i n k b)) = cstream A w xs := by
  obtain ⟨r,i,hi⟩ := pairedWords_replica_view (cstream A w xs)
    (by simpa only [length_cstream] using hlen) (cstream_pairBits_roundtrip hA w xs)
  exact ⟨(fun n k b => r k n b),(fun n k b => i k n b),hi⟩

/-- Numerical publication emits one ordered batch per key. Uniform row lengths
suffice to derive the router view of the actual concatenated streams. -/
theorem cstream_keyBatches_view {A N K L : ℕ} (hA : 4 ≤ A)
    (w : ℕ) (batches : Fin K → List (List GaussianInt))
    (hN : ∀ k, (batches k).length = N)
    (hL : ∀ k, ∀ xs ∈ batches k, xs.length = L) :
    ∃ r i : Fin N → Fin K → Fin (L*w) → Bool,
      keyReplicaWords (fun n k b => pairSym A (r n k b) (i n k b)) =
        (List.ofFn fun k => ((batches k).map (cstream A w)).flatten).flatten := by
  have hflatten (ys : List (List GaussianInt)) :
      cstream A w ys.flatten = (ys.map (cstream A w)).flatten := by
    induction ys with
    | nil => simp
    | cons zs ys ih => simp [ih]
  let zs := (List.ofFn fun k => (batches k).flatten).flatten
  have hb (k : Fin K) : ((batches k).flatten).length = N*L := by
    rw [List.length_flatten]
    have hm : (batches k).map List.length = List.replicate N L := by
      rw [←hN k]
      exact List.map_eq_replicate_iff.mpr (hL k)
    rw [hm,List.sum_replicate,smul_eq_mul]
  have hlen : zs.length*w = K*(N*(L*w)) := by
    have hz : zs.length = K*(N*L) := by
      simp [zs,List.length_flatten,hb,List.sum_ofFn]
    rw [hz]
    ac_rfl
  obtain ⟨r,i,hi⟩ := cstream_keyReplica_view hA w zs hlen
  refine ⟨r,i,?_⟩
  rw [hi]
  simp only [zs,hflatten,List.map_ofFn,Function.comp_def]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
