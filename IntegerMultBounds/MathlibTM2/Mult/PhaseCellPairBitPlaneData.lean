module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

/-- Recombination is exact whenever the input consists of pair symbols. -/
theorem pairBits_roundtrip {A : ℕ} (xs : List (Fin (A+4)))
    (hpair : ∀ x ∈ xs, pairSym A (pairRe x) (pairIm x) = x) :
    List.zipWith (pairSym A) (xs.map pairRe) (xs.map pairIm) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hpair x (by simp)
    have ht := ih (fun y hy => hpair y (by simp [hy]))
    simpa only [List.map_cons,List.zipWith_cons_cons,hx,ht]

/-- Packed coefficient streams satisfy the pair format without a `Fits` premise. -/
theorem cstream_pairBits_roundtrip {A : ℕ} (hA : 4 ≤ A) (w : ℕ) (zs : List GaussianInt) :
    List.zipWith (pairSym A) ((cstream A w zs).map pairRe) ((cstream A w zs).map pairIm) = cstream A w zs := by
  apply pairBits_roundtrip
  intro x hx
  obtain ⟨z,hz,hx⟩ := List.mem_flatMap.mp hx
  change x ∈ List.ofFn (fun i : Fin w => pairSym A _ _) at hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  simp only [pairRe_pairSym hA,pairIm_pairSym hA]

theorem replicaKeyPair_real {A N K W : ℕ} (hA : 4 ≤ A)
    (re im : Fin N → Fin K → Fin W → Bool) :
    (replicaKeyWords (fun r k b => pairSym A (re r k b) (im r k b))).map pairRealBit =
      replicaKeyWords (fun r k b => bitSymbol (re r k b)) := by
  rw [replicaKeyWords_map]
  simp only [pairRealBit,pairRe_pairSym hA]

theorem replicaKeyPair_imag {A N K W : ℕ} (hA : 4 ≤ A)
    (re im : Fin N → Fin K → Fin W → Bool) :
    (replicaKeyWords (fun r k b => pairSym A (re r k b) (im r k b))).map pairImagBit =
      replicaKeyWords (fun r k b => bitSymbol (im r k b)) := by
  rw [replicaKeyWords_map]
  simp only [pairImagBit,pairIm_pairSym hA]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
