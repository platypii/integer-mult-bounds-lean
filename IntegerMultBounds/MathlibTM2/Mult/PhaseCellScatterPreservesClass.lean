module

public import IntegerMultBounds.NLogN.PhaseCellNaturalClassSeparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScatterCoreRead

/-! Publishing a different length class preserves every encoded word on an
already published class, hence preserves its accuracy with no extra error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalScatterRows_preserves_class {A s : ℕ} [NeZero s] (t band L K q w : ℕ)
    (hLK : L ≠ K) (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : (naturalLengthGroup s t band L).length*(L*w) ≤ X.length)
    (n : Fin (naturalLengthGroup s t band K).length) (j : ZMod s)
    (hj : j ∈ publishedCellCore (naturalGroupOrigin s t band K n) K) :
    publishedCellRead q w (0 : ZMod s) (scatterRows (L*w) E X (naturalScatterGaps s t band L w)) j =
      publishedCellRead q w (0 : ZMod s) E j := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  have hiK : i < K := Finset.mem_range.mp hi
  let lo := naturalGroupOrigin s t band K n
  let phase := naturalGroupPhase s t band K n
  have hphase := naturalGroupPhase_mem s t band K n
  have hfit : lo.val+K ≤ s := by
    dsimp only [lo]
    rw [naturalGroupOrigin_val band K n]
    exact naturalOrigins_fit s t band K _ (List.mem_map.mpr ⟨_,hphase,rfl⟩)
  have his : i < s := by omega
  have hsum : lo.val+i < s := by omega
  have hval : (lo+(i : ZMod s)).val = lo.val+i := by
    rw [ZMod.val_add,ZMod.val_natCast,Nat.mod_eq_of_lt his,Nat.mod_eq_of_lt hsum]
  have hspan : naturalStart s t band phase ≤ (lo+(i : ZMod s)).val ∧
      (lo+(i : ZMod s)).val < naturalStart s t band phase+K := by
    rw [hval]
    have hh : lo.val = naturalStart s t band phase := naturalGroupOrigin_val band K n
    omega
  dsimp only [lo,phase] at hspan
  simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero]
  apply congrArg (fun ys : List (Fin (A+4)) => (value q (decodeWord ys)).re)
  apply List.ext_getElem?
  intro a
  by_cases ha : a < w
  · simp only [List.getElem?_take,ite_eq_left ha,List.getElem?_drop]
    apply scatterRows_absolute_off (L*w) (naturalSymbolOrigins s t band L w) E X
      (naturalSymbolOrigins_disjoint s t band L w)
      (fun p hp => (naturalSymbolOrigins_fit s t band L w p hp).trans hE)
      (by simpa [naturalSymbolOrigins] using hX)
    intro m hm
    obtain ⟨p,hp,hpval⟩ := List.mem_map.mp
      (List.getElem_mem hm : (naturalSymbolOrigins s t band L w)[m] ∈ naturalSymbolOrigins s t band L w)
    obtain ⟨cell,hcell,rfl⟩ := List.mem_map.mp hp
    rw [← hpval]
    rcases naturalClass_intervals_separated hLK hcell hphase with hsep | hsep
    · right
      have hh := Nat.mul_le_mul_right w (hsep.trans hspan.1)
      have hh' : naturalStart s t band cell*w+L*w ≤
          (naturalGroupOrigin s t band K n+(i : ZMod s)).val*w := by simpa only [Nat.add_mul] using hh
      exact hh'.trans (Nat.le_add_right _ _)
    · left
      have hh : (naturalGroupOrigin s t band K n+(i : ZMod s)).val+1 ≤ naturalStart s t band cell := by omega
      have hs := Nat.mul_le_mul_right w hh
      simp only [Nat.add_mul,Nat.one_mul] at hs
      omega
  · simp only [List.getElem?_take,ite_eq_right ha]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
