module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunMaskCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationMaskHeaders


/-! Generate the full publication mask and its workspace from ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def closedPublicationMask : Pr P₀ 117 Q A U :=
  closedHaloRunMask (pairSym A false false) (pairSym A true true)

def closedPublicationMaskCost (s t band a b : ℕ) : ℕ :=
  closedHaloRunMaskCost s t band a b

theorem closedPublicationMaskCost_le (s t band a b : ℕ) :
    closedPublicationMaskCost s t band a b ≤
      4000*(s+t+band+a+b+1)*(publicationGeometryWidth t band+4)^2 := by
  exact closedHaloRunMaskCost_le s t band a b

theorem closedPublicationMaskCost_halo_le {s t band a b : ℕ}
    (hst : s ≤ t) (hband : band ≤ s) (ha : a ≤ s) (hb : b ≤ s) :
    closedPublicationMaskCost s t band a b ≤ 4000*(5*t+1)*(4*Nat.size t+11)^2 := by
  exact closedHaloRunMaskCost_halo_le hst hband ha hb

theorem closedPublicationMask_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band)
    (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ closedPublicationMaskCost s t band a b ∧
      Exec body closedPublicationMask (mk v S) n
        (mk v' {S with R := Function.update S.R 109 (publicationMaskSymbols A s t band a b++S.R 109)}) := by
  have hm : (List.range s).map (fun k => if haloInteriorAt s t band a b k then
      pairSym A true true else pairSym A false false) = publicationMaskSymbols A s t band a b := by
    simp only [publicationMaskSymbols,couplingSourceMaskSymbols,haloMaskAt,Bool.false_eq_true,↓reduceIte]
    apply List.map_congr_left
    intro k hk
    cases haloInteriorAt s t band a b k <;> rfl
  simpa only [closedPublicationMask,closedPublicationMaskCost,hm] using
    closedHaloRunMask_exec hst haS hbS hA (pairSym A false false) (pairSym A true true)
      v S hs ht hband ha hb h115 h106 h108 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
