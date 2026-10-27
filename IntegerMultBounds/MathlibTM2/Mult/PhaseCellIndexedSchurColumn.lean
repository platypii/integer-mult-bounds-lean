module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySchurColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellResidentCoordinate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoordinateReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryWorkspace

/-! Generate a Schur column while the prepared folded page remains resident. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def indexedSchurColumn (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 151 Q A U :=
  .seq selectResidentCoordinate (.seq (boundarySchurColumn hR hQ) (uclear 139))

def indexedSchurColumnCost (p u l s t a b target n x : ℕ) : ℕ :=
  let V := publicationGeometryWidth t (PhaseCellBand.width p u)
  (n*(12*V+11)+27*V+6*x+36)+(generatedSchurColumnCost p u l s t a b target x+(2*x+2))

theorem indexedSchurColumn_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (n : ℕ) (hn : n < (haloBoundary s t (PhaseCellBand.width p u) a b).card)
    (v : HS 151 Q A U) (S : Stacks 151 A) (tail : List (Fin (A+4)))
    (pageTail : List (Fin (A+4)))
    (hindex : (S.R 0).length = n)
    (hpageWidth : (S.R 115).length = publicationGeometryWidth t (PhaseCellBand.width p u))
    (hpage : S.R 109 = cstream A (publicationGeometryWidth t (PhaseCellBand.width p u))
      ((bFoldOrder s (haloBoundary s t (PhaseCellBand.width p u) a b)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u (PhaseCellBand.width p u) 0 0 tail (embStk componentReg (embStk boundaryArithmeticReg {S with R := Function.update S.R 0 []})))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) :
    let j := bFoldAt s (haloBoundary s t (PhaseCellBand.width p u) a b) n
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let w := executionWidth p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
    ∃ v' m, ∃ D : ZMod s → GaussianInt,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
      let output := cstream A w (chirpLine s C)++tail
      let S' : Stacks 151 A := {S with R := (Function.update (Function.update S.R 0 []) 110 output)}
      v'.user = v.user ∧ m ≤ indexedSchurColumnCost p u l s t a b target n j.val ∧
      Exec (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))) (indexedSchurColumn hR hQ) (mk v S) m (mk v' S') ∧
      (∀ i, (C i).im = 0) ∧
      (∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^couplingRowExponent 2 (stableInteriorExponent p 2)
        (8*p+1) (couplingCountExponent p u)) ∧
      (∀ i ∈ haloBoundary s t band a b,
        |publishedCellRead q w (0 : ZMod s) (S'.R 110) i-
          (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
            (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^target) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
        q l s t u band 0 0 output (embStk componentReg (embStk boundaryArithmeticReg S')) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let V := publicationGeometryWidth t band
  let j := bFoldAt s (haloBoundary s t band a b) n
  let S₀ : Stacks 151 A := {S with R := Function.update S.R 0 []}
  have hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = [] := by
    intro r hr1 hr7
    have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [embStk,componentReg,boundaryArithmeticReg] using hready.blank 1 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg] using hready.blank 2 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg] using hready.blank 3 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg] using hready.blank 4 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg] using hready.blank 5 (by decide) (by decide) (by decide)
    · simpa [embStk,componentReg,boundaryArithmeticReg] using hready.blank 6 (by decide) (by decide) (by decide)
  have h106 : S.R 106 = [] := by
    have hh := hready.blank 106 (by decide) (by decide) (by decide)
    simpa [embStk,componentReg,boundaryArithmeticReg] using hh
  have hsfit : s ≤ 2^V := by
    have hh := publicationGeometryWidth_fits t band
    nlinarith only [hh,hst]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hj,hpos⟩ := selectResidentCoordinate_exec
    (body := embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
    (haloBoundary s t band a b) V n (by omega) hsfit hn pageTail v S hindex hpageWidth hpage h106 h139 hblank
  let coordinate := List.replicate j.val (tick : Fin (A+4))
  let S₁ : Stacks 151 A := {S₀ with R := Function.update S₀.R 139 coordinate}
  have hready₁ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u target 2) 2) l s t u band 0 0 tail
      (embStk componentReg (embStk boundaryArithmeticReg S₁)) := by
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg
      (embStk boundaryArithmeticReg {S₀ with R := Function.update S₀.R (boundaryArithmeticReg 139) coordinate}))
    rw [boundaryArithmeticProject_updateR_inner]
    convert hready.update_coordinate coordinate using 1
    exact componentProject_updateR_inner (embStk boundaryArithmeticReg S₀) (139 : Fin 144) coordinate
  obtain ⟨v₂,m₂,D,hu₂,hm₂,he₂,hreal,hnorm,herror,hready₂⟩ := boundarySchurColumn_spec (body := body)
    hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband has hbs hpad j hj v₁ S₁ tail hready₁
    (by simpa [S₁,S₀] using haMaster) (by simpa [S₁,S₀] using hbMaster)
    (by simp [S₁,coordinate]) (by simpa [S₁,S₀] using h127) (by simpa [S₁,S₀] using h138)
    (by simpa [S₁,S₀] using h143) (by simpa [S₁,S₀] using h147)
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let B := couplingRowField (2^15*p) q t u band a b true (negativeUnitField q j) (fun _ => 0)
  let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (B i))
  let output := cstream A w (chirpLine s C)++tail
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 110 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec
    (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))) 139 v₂ S₂
  let S₃ : Stacks 151 A := {S₂ with R := Function.update S₂.R 139 []}
  let Sfinal : Stacks 151 A := {S₀ with R := Function.update S₀.R 110 output}
  have hframe : S₃ = Sfinal := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk0 : k = 0 <;> by_cases hk110 : k = 110 <;> by_cases hk139 : k = 139 <;>
      simp_all [S₃,S₂,S₁,S₀,Sfinal]
  have hlen : (S₂.R 139).length = j.val := by simp [S₂,S₁,coordinate]
  have he₃' : Exec (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body)))
      (uclear 139) (mk v₂ S₂) (2*j.val+2) (mk v₃ Sfinal) := by
    rw [← hframe]
    simpa only [hlen] using he₃
  have hready₃ : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u target 2) 2+1)
      q l s t u band 0 0 output (embStk componentReg (embStk boundaryArithmeticReg Sfinal)) := by
    rw [← hframe]
    change LengthKeyReady _ _ _ _ _ _ _ _ _ _ _ (embStk componentReg
      (embStk boundaryArithmeticReg {S₂ with R := Function.update S₂.R (boundaryArithmeticReg 139) []}))
    rw [boundaryArithmeticProject_updateR_inner]
    convert hready₂.update_coordinate [] using 1
    exact componentProject_updateR_inner (embStk boundaryArithmeticReg S₂) (139 : Fin 144) []
  refine ⟨v₃,m₁+(m₂+(2*j.val+2)),D,hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add hm₁ (Nat.add_le_add_right hm₂ _),Exec.seq he₁ (Exec.seq he₂ he₃'),hreal,hnorm,?_,hready₃⟩
  simpa [S₂,S₁,S₀,Sfinal,output,C,B,q,w,band,j] using herror

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
