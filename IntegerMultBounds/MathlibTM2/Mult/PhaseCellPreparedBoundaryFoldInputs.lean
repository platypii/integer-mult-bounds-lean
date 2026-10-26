module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldCounters

/-! Prepare boundary coordinates and all fold counters from ordinary geometry headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedBoundaryFoldInputs : Pr P₀ 117 Q A U :=
  .seq preparedBoundaryOrder boundaryFoldCounters

def preparedBoundaryFoldInputsCost (s t band a b : ℕ) [NeZero s] : ℕ :=
  preparedBoundaryOrderCost s t band a b+
    boundaryFoldCountersCost (haloBoundary s t band a b).card (publicationGeometryWidth t band)

theorem preparedBoundaryFoldInputs_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = [])
    (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    let V := publicationGeometryWidth t band
    let n := (haloBoundary s t band a b).card
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedBoundaryFoldInputsCost s t band a b ∧
      Exec body preparedBoundaryFoldInputs (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update
          (Function.update (Function.update (Function.update S.R 115 (List.replicate V tick))
            109 (boundaryOrderSymbols A V s t band a b)) 116 (List.replicate n tick))
            0 (List.replicate (n/2) tick)) 2 (List.replicate ((n+1)/2-n/2) tick))
            3 (List.replicate (((n+1)/2)*V) tick))}) := by
  dsimp only
  let V := publicationGeometryWidth t band
  let n := (haloBoundary s t band a b).card
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := preparedBoundaryOrder_exec (body := body)
    hst haS hbS hbandS v S hs ht hband ha hb h115 h116 h109 h106 h108 hblank
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update
    (Function.update S.R 115 (List.replicate V tick)) 109 (boundaryOrderSymbols A V s t band a b))
      116 (List.replicate n tick))}
  have hlow (r : Fin 117) (hr : r.val < 6) : S₁.R r = [] := by
    have h115' : r ≠ 115 := by intro he; subst r; norm_num at hr
    have h109' : r ≠ 109 := by intro he; subst r; norm_num at hr
    have h116' : r ≠ 116 := by intro he; subst r; norm_num at hr
    simpa [S₁,h115',h109',h116'] using hblank r (by omega)
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := boundaryFoldCounters_exec (body := body)
    n V v₁ S₁ (by simp [S₁]) (by simp [S₁]) hlow
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
