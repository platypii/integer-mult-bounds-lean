module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBoundaryFold

/-! Place the procedure-free coordinate-page constructor in the table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def tableFoldReg (i : Fin 148) : Fin 154 := ⟨i.val,by omega⟩
theorem tableFoldReg_injective : Function.Injective tableFoldReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 154 => k.val) h)

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def tableBoundaryFold : Pr P 154 Q A U :=
  embProg tableFoldReg Empty.elim (closedBoundaryFold (P₀ := Empty))

theorem tableBoundaryFold_exec {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hs : (S.R 97).length = s) (ht : (S.R 98).length = t)
    (hband : (S.R 100).length = band) (ha : (S.R 101).length = a) (hb : (S.R 103).length = b)
    (h115 : S.R 115 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = [])
    (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 154, r.val < 77 → S.R r = [])
    (hleft : ∀ r : Fin 148, S.L (tableFoldReg r) = []) :
    let V := publicationGeometryWidth t band
    let n := (haloBoundary s t band a b).card
    let output := cstream A V ((bFoldOrder s (haloBoundary s t band a b)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    ∃ v' m, v'.user = v.user ∧ m ≤ closedBoundaryFoldCost s t band a b ∧
      Exec body tableBoundaryFold (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          115 (List.replicate V tick)) 116 (List.replicate n tick)) 109 output)}) := by
  dsimp only
  obtain ⟨v₁,m,hu₁,hm,he₁⟩ := closedBoundaryFold_exec (body := fun e : Empty => nomatch e)
    hst haS hbS hbandS (embDn tableFoldReg v) (embStk tableFoldReg S)
    (by simpa [embStk,tableFoldReg] using hs) (by simpa [embStk,tableFoldReg] using ht)
    (by simpa [embStk,tableFoldReg] using hband) (by simpa [embStk,tableFoldReg] using ha)
    (by simpa [embStk,tableFoldReg] using hb) (by simpa [embStk,tableFoldReg] using h115)
    (by simpa [embStk,tableFoldReg] using h116) (by simpa [embStk,tableFoldReg] using h109)
    (by simpa [embStk,tableFoldReg] using h106) (by simpa [embStk,tableFoldReg] using h108)
    (by intro r hr; exact hblank _ hr) hleft
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (e := tableFoldReg) (ι := Empty.elim) (body' := body)
    tableFoldReg_injective (fun e => nomatch e) he₁ v rfl S rfl
  refine ⟨v₂,m,hu₂.trans hu₁,hm,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let B := embStk tableFoldReg S
  let B₁ : Stacks 148 A := {B with R := Function.update B.R 115 (List.replicate (publicationGeometryWidth t band) tick)}
  let B₂ : Stacks 148 A := {B₁ with R := Function.update B₁.R 116 (List.replicate (haloBoundary s t band a b).card tick)}
  rw [embOvr_updR tableFoldReg_injective B₂ S 109 _,
    embOvr_updR tableFoldReg_injective B₁ S 116 _,
    embOvr_updR tableFoldReg_injective B S 115 _,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
