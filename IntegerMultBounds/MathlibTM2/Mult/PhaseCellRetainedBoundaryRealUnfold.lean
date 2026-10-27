module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundarySolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPublicationReady

/-! Execute the retained boundary solve and inverse fold and real-project its computed output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryRealUnfold (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundarySolve hR hQ) boundaryRealUnfold

theorem retainedBoundaryRealUnfold_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s) (has : a ≤ s) (hbs : b ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt) (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (h109 : S.R 109 = []) (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0 (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2) (chirpLine s F)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = []) 
    (h151 : S.R 151 = []) (h153 : S.R 153 = [])
    (h152 : S.R 152 = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let B := haloBoundary s t (PhaseCellBand.width p u) a b
    let bits := boundaryTableBits p target 2 B.card
    let band := PhaseCellBand.width p u
    let W := 12*band+1
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v₁ S₁ n₁ v' S' n, ∃ D : ZMod s → GaussianInt, ∃ columns : List (ZMod s → GaussianInt),
    ∃ solution : List GaussianInt,
      let C := couplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))
      v'.user = v.user ∧ n₁ ≤ retainedBoundarySolveCost p u l s t a b target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundarySolve hR hQ)
        (mk v S) n₁ (mk v₁ S₁) ∧
      n ≤ retainedBoundarySolveCost p u l s t a b target+
        (2*(([189,191,198,204] : List (Fin 224)).map fun i => (S₁.R i).length).sum+9)+
          generatedBoundaryUnfoldCost B.card w+(B.card*(12*w+9)+12) ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryRealUnfold hR hQ)
        (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧ solution.length = B.card ∧
      S'.R 204 = cstream A w ((bOrder s B).map (boundarySolutionField B solution)) ∧ S'.R 217 = [] ∧
      S'.R 110 = cstream A w (chirpLine s C)++S.R 110 ∧
      S'.R 132 = bandTableWords A w B W columns 0++cstream A w (chirpLine s D)++S.R 132 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      BoundaryPublicationReady S' s B.card (publicationGeometryWidth t band) w ∧
      S'.R 109 = cstream A (publicationGeometryWidth t band) ((bFoldOrder s B).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt))) ∧
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      (∀ i ∈ B, |(value q (boundarySolutionField B solution i)).re-x i| ≤ 3/(2 : ℝ)^target) ∧
      (∀ i, ‖value q (boundarySolutionField B solution i)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧
      (∀ i, Fits w (boundarySolutionField B solution i)) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₁,S₁,n₁,D,columns,solution,hu₁,hn₁,he₁,hlen,hsolLen,hfit,hsrc,h110,h132,
    hinp,hout,hL,hlegacy,hready₁,h119,hreset,hcount,hmul,h184,h223,h220,h221,h206,hcoords,h115,h116,hacc⟩ :=
    retainedBoundarySolve_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad F hF v S tail h109 h115 h116 hleft hready haMaster hbMaster
      h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  have hleft₁ : ∀ i, S₁.L i = [] := by intro i; rw [hL]; exact hleft i
  have hc : ∀ i ∈ ([184,223,208,211,201,215] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h184
    · exact h223
    · simpa [boundaryFactorState,boundaryFactorReg] using hreset.empty .ya (by simp [boundarySolveScratch])
    · simpa [boundaryFactorState,boundaryFactorReg] using hreset.empty .xs (by simp [boundarySolveScratch])
    · simpa [boundaryFactorState,boundaryFactorReg] using hreset.empty .tC (by simp [boundarySolveScratch])
    · simpa [boundaryFactorState,boundaryFactorReg] using hreset.empty .ac2 (by simp [boundarySolveScratch])
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryRealUnfold_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) (by omega) w B solution hsolLen v₁ S₁ hleft₁ hmul
    hcount hsrc hready₁.wn hc
  let S₀ : Stacks 224 A := {S₁ with R := fun i => if i ∈ ([189,191,198,204] : List (Fin 224)) then [] else S₁.R i}
  let S₂ : Stacks 224 A := {S₀ with R := (Function.update (Function.update S₀.R 217 []) 204
    (cstream A w ((bOrder s B).map (boundarySolutionField B solution))))}
  have hmFinal : ∀ i : Fin 64, S₂.R (boundaryFactorMulReg i) = [] := by
    intro i
    have ho (j : Fin 224) (hj : 64 ≤ j.val) : boundaryFactorMulReg i ≠ j := by
      intro h
      have hv := congrArg (fun k : Fin 224 => k.val) h
      change i.val = j.val at hv
      have hi := i.isLt
      omega
    simpa [S₂,S₀,ho 189 (by decide),ho 191 (by decide),ho 198 (by decide),
      ho 204 (by decide),ho 217 (by decide)] using hmul i
  have hpub : BoundaryPublicationReady S₂ s B.card (publicationGeometryWidth t (PhaseCellBand.width p u)) w := by
    refine ⟨hleft₁,hmFinal,?_,?_,?_,?_,?_⟩
    · have hs : (S.R 121).length = s := by
        simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
          hready.masters (121,97) (by simp [groupHeaderCopies])
      have hf : S₁.R 121 = S.R 121 := hlegacy 121 (by decide) (by decide) (by decide) (by decide) (by decide)
      simpa [S₂,S₀,hf] using hs
    · simpa [S₂,S₀,boundaryFactorState,boundaryFactorReg] using hready₁.wn
    · simpa [S₂,S₀] using congrArg List.length h115
    · simpa [S₂,S₀] using h116
    · intro i hi
      have hm : i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 224)) ∨
          i ∈ ([184,217,223,201,208,211,215,220,206] : List (Fin 224)) := List.mem_append.mp hi
      rcases hm with hm | hm
      · have hlt : i.val < 64 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
          rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact hmFinal ⟨i.val,hlt⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · simpa [S₂,S₀] using h184
        · simp [S₂]
        · simpa [S₂,S₀] using h223
        · simpa [S₂,S₀] using hc 201 (by simp)
        · simpa [S₂,S₀] using hc 208 (by simp)
        · simpa [S₂,S₀] using hc 211 (by simp)
        · simpa [S₂,S₀] using hc 215 (by simp)
        · simpa [S₂,S₀] using h220
        · simpa [S₂,S₀] using h206
  have hn : n₁+n₂ ≤ retainedBoundarySolveCost p u l s t a b target+
      (2*(([189,191,198,204] : List (Fin 224)).map fun i => (S₁.R i).length).sum+9)+
        generatedBoundaryUnfoldCost B.card w+(B.card*(12*w+9)+12) := by
    simpa only [Nat.add_assoc] using Nat.add_le_add hn₁ hn₂
  refine ⟨v₁,S₁,n₁,v₂,S₂,n₁+n₂,D,columns,solution,hu₂.trans hu₁,hn₁,he₁,hn,
    Exec.seq he₁ he₂,hlen,hsolLen,?_,?_,?_,?_,hinp,hout,hL,hpub,?_,?_⟩
  · simp [S₂,w,bits,B]
  · simp [S₂,w,bits,B]
  · simpa [S₂,S₀] using h110
  · simpa [S₂,S₀] using h132
  · simpa [S₂,S₀] using hcoords
  · intro x hx
    have ha := hacc x hx
    exact ⟨boundarySolutionField_error q B solution x _ (fun i hi => (ha i hi).1),
      boundarySolutionField_magnitude q _ B solution (fun i hi => (ha i hi).2),
      boundarySolutionField_fits w B solution hsolLen hfit⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
