module

public import IntegerMultBounds.NLogN.PhaseCellHaloClassSeparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloScatterCoreRead

/-! Publishing a different length class preserves every encoded word on an
already published class, hence preserves its accuracy with no extra error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloScatterRows_preserves_class {A s : ℕ} [NeZero s] (t band a b L K q w : ℕ)
    (hLK : L ≠ K) (E X : List (Fin (A+4))) (hE : s*w ≤ E.length)
    (hX : (haloLengthGroup s t band a b L).length*(L*w) ≤ X.length)
    (n : Fin (haloLengthGroup s t band a b K).length) (j : ZMod s)
    (hj : j ∈ publishedCellCore (haloGroupOrigin s t band a b K n) K) :
    publishedCellRead q w (0 : ZMod s) (scatterRows (L*w) E X (haloScatterGaps s t band a b L w)) j =
      publishedCellRead q w (0 : ZMod s) E j := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
  have hiK : i < K := Finset.mem_range.mp hi
  let lo := haloGroupOrigin s t band a b K n
  let phase := haloGroupPhase s t band a b K n
  have hphase := haloGroupPhase_mem s t band a b K n
  have hfit : lo.val+K ≤ s := by
    dsimp only [lo]
    rw [haloGroupOrigin_val band a b K n]
    exact haloOrigins_fit s t band a b K _ (List.mem_map.mpr ⟨_,hphase,rfl⟩)
  have his : i < s := by omega
  have hsum : lo.val+i < s := by omega
  have hval : (lo+(i : ZMod s)).val = lo.val+i := by
    rw [ZMod.val_add,ZMod.val_natCast,Nat.mod_eq_of_lt his,Nat.mod_eq_of_lt hsum]
  have hspan : haloStart s t band a phase ≤ (lo+(i : ZMod s)).val ∧
      (lo+(i : ZMod s)).val < haloStart s t band a phase+K := by
    rw [hval]
    have hh : lo.val = haloStart s t band a phase := haloGroupOrigin_val band a b K n
    omega
  dsimp only [lo,phase] at hspan
  simp only [publishedCellRead,ZMod.val_zero,Nat.sub_zero]
  apply congrArg (fun ys : List (Fin (A+4)) => (value q (decodeWord ys)).re)
  apply List.ext_getElem?
  intro z
  by_cases hz : z < w
  · simp only [List.getElem?_take,ite_eq_left hz,List.getElem?_drop]
    apply scatterRows_absolute_off (L*w) (haloSymbolOrigins s t band a b L w) E X
      (haloSymbolOrigins_disjoint s t band a b L w)
      (fun p hp => (haloSymbolOrigins_fit s t band a b L w p hp).trans hE)
      (by simpa [haloSymbolOrigins] using hX)
    intro m hm
    obtain ⟨p,hp,hpval⟩ := List.mem_map.mp
      (List.getElem_mem hm : (haloSymbolOrigins s t band a b L w)[m] ∈ haloSymbolOrigins s t band a b L w)
    obtain ⟨cell,hcell,rfl⟩ := List.mem_map.mp hp
    rw [← hpval]
    rcases haloClass_intervals_separated hLK hcell hphase with hsep | hsep
    · right
      have hh := Nat.mul_le_mul_right w (hsep.trans hspan.1)
      have hh' : haloStart s t band a cell*w+L*w ≤
          (haloGroupOrigin s t band a b K n+(i : ZMod s)).val*w := by simpa only [Nat.add_mul] using hh
      exact hh'.trans (Nat.le_add_right _ _)
    · left
      have hh : (haloGroupOrigin s t band a b K n+(i : ZMod s)).val+1 ≤ haloStart s t band a cell := by omega
      have hs := Nat.mul_le_mul_right w hh
      simp only [Nat.add_mul,Nat.one_mul] at hs
      omega
  · simp only [List.getElem?_take,ite_eq_right hz]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
