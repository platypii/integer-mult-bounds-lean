module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval

/-! A short principal interval needs only its own words and zero padding.
The separation hypothesis rules out a stencil wrapping back into the interval. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- An active cyclic stencil coordinate is in the unwrapped local payload. -/
theorem localRibbon_active_index {s a N band i : ℕ} [NeZero s]
    (hfit : a+N ≤ s) (hsep : N+band ≤ s) (hi : i < N+2*band)
    (hin : a ≤ ((a+i : ZMod s)-(band : ZMod s)).val ∧
      ((a+i : ZMod s)-(band : ZMod s)).val < a+N) :
    band ≤ i ∧ i < band+N := by
  by_cases hleft : a+i < band
  · have hm : s+a+i-band < s := by omega
    have he : ((s+a+i-band : ℕ) : ZMod s) = (a+i : ZMod s)-(band : ZMod s) := by
      rw [Nat.cast_sub (by omega : band ≤ s+a+i)]
      simp [Nat.cast_add]
    rw [← he,ZMod.val_cast_of_lt hm] at hin
    omega
  · have hnonneg : band ≤ a+i := by omega
    have he : (a+i : ZMod s)-(band : ZMod s) = ((a+i-band : ℕ) : ZMod s) := by
      rw [Nat.cast_sub hnonneg,Nat.cast_add]
    by_cases hright : a+i-band < s
    · rw [he,ZMod.val_cast_of_lt hright] at hin
      omega
    · have hs : s ≤ a+i-band := by omega
      have hm : a+i-band-s < s := by omega
      rw [he,ZMod.val_natCast,Nat.mod_eq_sub_mod hs,Nat.mod_eq_of_lt hm] at hin
      omega

def localCouplingRibbon {s : ℕ} (band a N : ℕ) (C : ZMod s → GaussianInt) : List GaussianInt :=
  List.replicate band 0++packedInterval a N C++List.replicate band 0

@[simp] theorem localCouplingRibbon_length {s band a N : ℕ} (C : ZMod s → GaussianInt)
    (hfit : a+N ≤ s) : (localCouplingRibbon band a N C).length = N+2*band := by
  simp [localCouplingRibbon,packedInterval_length C hfit]; omega

theorem maskedLine_localCouplingRibbon {s : ℕ} [NeZero s] (boundary : Bool)
    (t band a N : ℕ) (C : ZMod s → GaussianInt)
    (hfit : a+N ≤ s) (hsep : N+band ≤ s) :
    maskedLine (couplingRibbonFlags (s := s) boundary t band a (a+N) a N)
      (localCouplingRibbon band a N C) =
      couplingSourceInterval boundary t band a (a+N) a N C := by
  let T := if boundary then haloBoundary s t band a (a+N) else haloInterior s t band a (a+N)
  have hsub : T ⊆ haloVertices s a (a+N) := by
    dsimp only [T]
    split
    · exact Finset.sdiff_subset
    · exact haloInterior_subset s t band a (a+N)
  have hflags : (couplingRibbonFlags (s := s) boundary t band a (a+N) a N).length = N+2*band := by
    simp only [couplingRibbonFlags,cyclicPaddedLine,List.length_take,List.length_drop,List.length_map,List.length_range]
    omega
  have hlen : (localCouplingRibbon band a N C).length =
      (couplingRibbonFlags (s := s) boundary t band a (a+N) a N).length := by
    rw [localCouplingRibbon_length C hfit,hflags]
  apply List.ext_getElem
  · rw [maskedLine_length _ _ hlen,hflags,couplingSourceInterval_length _ _ _ _ _ _ _ _ hfit]
  · intro i hi hj
    have hiN : i < N+2*band := by
      simpa only [maskedLine_length _ _ hlen,hflags] using hi
    rw [maskedLine_getElem _ _ hlen i (by omega)]
    simp only [couplingRibbonFlags,couplingSourceInterval,cyclicPaddedLine,List.getElem_take,
      List.getElem_drop,List.getElem_map,List.getElem_range]
    simp only [Nat.cast_add]
    change (if decide (((a+i : ZMod s)-(band : ZMod s)) ∈ T) then
      (localCouplingRibbon band a N C)[i]'(by rw [localCouplingRibbon_length C hfit]; exact hiN) else 0) =
      (if ((a+i : ZMod s)-(band : ZMod s)) ∈ T then C ((a+i : ZMod s)-(band : ZMod s)) else 0)
    by_cases hk : ((a+i : ZMod s)-(band : ZMod s)) ∈ T
    · have hbounds := (mem_haloVertices a (a+N) _).mp (hsub hk)
      have hidx := localRibbon_active_index hfit hsep hiN hbounds
      simp only [hk,decide_true,Bool.true_eq,ite_true]
      have hleft : ¬ i < band := by omega
      have hmid : i-band < N := by omega
      simp only [localCouplingRibbon,List.getElem_append,List.length_append,List.length_replicate,
        packedInterval_length C hfit,hleft,hidx.2,dite_false,dite_true]
      rw [packedInterval_get C hfit hmid]
      congr 1
      rw [Nat.cast_add,Nat.cast_sub hidx.1]
      push_cast
      ring
    · simp only [hk,decide_false,Bool.false_eq_true,ite_false]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
