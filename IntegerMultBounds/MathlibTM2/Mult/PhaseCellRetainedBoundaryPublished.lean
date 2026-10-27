module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryReleaseVolume

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedBoundaryRealUnfold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryPublish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRecoveryReady

/-! Execute the accurate retained boundary solve through ambient publication. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def retainedBoundaryPublished (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (retainedBoundaryRealUnfold hR hQ) preparedBoundaryPublish

noncomputable def retainedBoundaryPublishedCost (p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p target 2 N
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let V := publicationGeometryWidth t band
  retainedBoundaryRealUnfoldCost p u l s t a b target+9+generatedBoundaryUnfoldCost N V+
    (4*(N*V)+4)+generateBoundaryAdvancesCost N V w s+93*s*w+45

theorem retainedBoundaryPublished_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∃ v' S' n, ∃ D : ZMod s → GaussianInt,
    ∃ columns : List (ZMod s → GaussianInt), ∃ solution : List GaussianInt,
      let C := guardedCouplingRowField (2^15*p) q t u band a b false D (fun i => realPartWord (F i))
      let G := boundarySolutionField B solution
      v'.user = v.user ∧
      n ≤ retainedBoundaryPublishedCost p u l s t a b target ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (retainedBoundaryPublished hR hQ)
        (mk v S) n (mk v' S') ∧
      columns.length = B.card ∧ solution.length = B.card ∧
      S'.R 132 = cstream A w (chirpLine s G)++
        (bandTableWords A w B W columns 0++cstream A w (chirpLine s D)++S.R 132) ∧
      S'.R 110 = cstream A w (chirpLine s C)++S.R 110 ∧
      S'.R 109 = [] ∧ S'.R 204 = [] ∧ S'.R 206 = [] ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i : Fin 154, i ≠ 110 → i ≠ 115 → i ≠ 116 → i ≠ 132 →
        S'.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i)) ∧
      LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u bits 2) 2+1)
        q l s t u band 0 0 (S'.R 110)
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S')))) ∧
      (S'.R 141).length = a ∧ (S'.R 142).length = b ∧
      S'.R 127 = [] ∧ S'.R 138 = [] ∧ S'.R 143 = [] ∧
      BoundaryRetirementReady S' s B.card W w ∧
      (boundaryOwnedRegs.map fun i => (S'.R i).length).sum ≤
        boundaryOwnedRegs.length*(publicationGeometryWidth t band+B.card+boundaryPermanentSizeBound q band B.card) ∧
      ∀ x : ZMod s → ℝ,
      SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (F i)).re) →
      (∀ i ∈ B, |publishedCellRead q w (0 : ZMod s) (S'.R 132) i-x i| ≤ 3/(2 : ℝ)^target) ∧
      (∀ i, (G i).im = 0) ∧
      (∀ i, ‖value q (G i)‖ ≤ (2 : ℝ)^stableInteriorExponent p 2) ∧
      (∀ i, Fits w (G i)) := by
  dsimp only
  let B := haloBoundary s t (PhaseCellBand.width p u) a b
  let band := PhaseCellBand.width p u
  let V := publicationGeometryWidth t band
  let bits := boundaryTableBits p target 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨v₁,S₁,n₁,D,columns,solution,hu₁,hn₁,he₁,hlen,hsolLen,hsrc,h217,
    h110,h132,hinp,hout,hL,hlegacy,hpub,hcoords,hretire₁,hperm,hzero,hacc⟩ :=
    retainedBoundaryRealUnfold_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
      hband has hbs hpad F hF v S tail h109 h115 h116 hleft hready haMaster hbMaster
      h0 h139 h127 h138 h143 h147 h151 h153 h152 hnew
  let G := boundarySolutionField B solution
  have hw : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hsV : s ≤ 2^V := by
    have hh := publicationGeometryWidth_fits t band
    change 8*(t+1)^2+2*band+8 < 2^V at hh
    nlinarith only [hh,hst]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := preparedBoundaryPublish_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) (by omega) s B V w hw hsV G
    (fun i hi => boundarySolutionField_off B solution i hi) [] v₁ S₁
    hpub.left hpub.mul hpub.ambient hpub.width hpub.geometry hpub.count hcoords
    (by simpa only [List.append_nil] using hsrc) hpub.scratch
  let S₂base : Stacks 224 A := {S₁ with R := fun i => if i ∈ ([189,191,198] : List (Fin 224)) then [] else S₁.R i}
  let S₂ : Stacks 224 A := {S₂base with R := (Function.update (Function.update (Function.update (Function.update S₂base.R
    109 []) 206 []) 204 []) 132 (cstream A w (chirpLine s G)++S₁.R 132))}
  have hframe (i : Fin 154) (hi109 : i ≠ 109) (hi110 : i ≠ 110)
      (hi115 : i ≠ 115) (hi116 : i ≠ 116) (hi132 : i ≠ 132) :
      S₂.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i) := by
    have ho (j : Fin 224) (hj : 154 ≤ j.val) : boundaryFactorLegacyReg i ≠ j := by
      intro h
      have hv := congrArg (fun k : Fin 224 => k.val) h
      change i.val = j.val at hv
      have hi := i.isLt
      omega
    have h109 : boundaryFactorLegacyReg i ≠ 109 := by simpa [boundaryFactorLegacyReg,Fin.ext_iff] using hi109
    have h132 : boundaryFactorLegacyReg i ≠ 132 := by simpa [boundaryFactorLegacyReg,Fin.ext_iff] using hi132
    simpa [S₂,S₂base,h109,h132,ho 189 (by decide),ho 191 (by decide),ho 198 (by decide),
      ho 204 (by decide),ho 206 (by decide)] using hlegacy i hi109 hi110 hi115 hi116 hi132
  have hready₂ := boundaryRecoveryReady_of_frame (S' := S₂) hready hinp hout hL hframe
  have hretire₂ : BoundaryRetirementReady S₂ s B.card (12*band+1) w := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa [S₂,S₂base] using hretire₁.ambient
    · simpa [S₂,S₂base] using hretire₁.rows
    · simpa [S₂,S₂base] using hretire₁.band
    · simpa [S₂,S₂base] using hretire₁.width
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₂,S₂base] using hretire₁.scratch _ (by simp)
  have hperm₂ : BoundaryPermanentBound (boundaryFactorState S₂) (boundaryPermanentSizeBound q band B.card) := by
    intro r hr
    have ho (k : RsbR) (hk : k ∈ boundaryTransientRoles) : boundaryFactorReg r ≠ boundaryFactorReg k := by
      intro he
      have hh := boundaryFactorReg_injective he
      subst r
      exact hr hk
    have h189 : boundaryFactorReg r ≠ 189 := ho .m2wn (by simp [boundaryTransientRoles])
    have h191 : boundaryFactorReg r ≠ 191 := ho .kn (by simp [boundaryTransientRoles])
    have h198 : boundaryFactorReg r ≠ 198 := ho .tK (by simp [boundaryTransientRoles])
    have h204 : boundaryFactorReg r ≠ 204 := ho .sel (by simp [boundaryTransientRoles])
    have h206 : boundaryFactorReg r ≠ 206 := ho .vk (by simp [boundaryTransientRoles])
    have h109 : boundaryFactorReg r ≠ 109 := boundaryFactorReg_off r 109 (by decide)
    have h132 : boundaryFactorReg r ≠ 132 := boundaryFactorReg_off r 132 (by decide)
    simpa [S₂,S₂base,boundaryFactorState,h189,h191,h198,h204,h206,h109,h132] using hperm r hr
  have hvolume : (boundaryOwnedRegs.map fun i => (S₂.R i).length).sum ≤
      boundaryOwnedRegs.length*(V+B.card+boundaryPermanentSizeBound q band B.card) := by
    apply boundaryReleaseVolume_le S₂ hperm₂
    · have hh : (S₁.R 115).length = V := hpub.geometry
      simpa [S₂,S₂base] using hh.le
    · exact hretire₂.rows.le
    · intro r hr hrsrc
      simp only [boundaryTransientRoles,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact False.elim (hrsrc rfl)
      · simp [S₂,S₂base,boundaryFactorState,boundaryFactorReg]
      · simp [S₂,S₂base,boundaryFactorState,boundaryFactorReg]
      · simp [S₂,S₂base,boundaryFactorState,boundaryFactorReg]
      · simp [S₂,S₂base,boundaryFactorState,boundaryFactorReg]
      · simp [S₂,S₂base,boundaryFactorState,boundaryFactorReg]
      · simpa [S₂,S₂base,boundaryFactorState,boundaryFactorReg] using h217
    · exact hretire₂.scratch 184 (by simp)
    · simpa [S₂,S₂base] using hpub.scratch 223 (by simp)
  have hcost₂ : n₂ ≤ 9+generatedBoundaryUnfoldCost B.card V+(4*(B.card*V)+4)+
      generateBoundaryAdvancesCost B.card V w s+93*s*w+45 := by
    simpa only [hzero,Nat.mul_zero,Nat.zero_add] using hn₂
  have hn : n₁+n₂ ≤ retainedBoundaryPublishedCost p u l s t a b target := by
    simpa only [retainedBoundaryPublishedCost,Nat.add_assoc] using Nat.add_le_add hn₁ hcost₂
  refine ⟨v₂,S₂,n₁+n₂,D,columns,solution,hu₂.trans hu₁,?_,
    Exec.seq he₁ he₂,hlen,hsolLen,?_,?_,?_,?_,?_,hinp,hout,hL,?_,hready₂,?_,?_,?_,?_,?_,hretire₂,hvolume,?_⟩
  · simpa only [Nat.add_assoc] using hn
  · simp [S₂,S₂base,h132,List.append_assoc,w,bits,B,G]
  · simpa [S₂,S₂base] using h110
  · simp [S₂]
  · simp [S₂]
  · simp [S₂]
  · intro i hi110 hi115 hi116 hi132
    by_cases hi109 : i = 109
    · subst i; simp [S₂,boundaryFactorLegacyReg,h109]
    · exact hframe i hi109 hi110 hi115 hi116 hi132
  · have hf : S₂.R 141 = S.R 141 := hframe 141 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact haMaster
  · have hf : S₂.R 142 = S.R 142 := hframe 142 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hf]
    exact hbMaster
  · exact (hframe 127 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h127
  · exact (hframe 138 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h138
  · exact (hframe 143 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h143
  · intro x hx
    obtain ⟨herror,hmag,hfit⟩ := hacc x hx
    refine ⟨?_,fun i => boundarySolutionField_im B solution i,hmag,hfit⟩
    intro i hi
    have hread := publishedCellRead_encodedField (q := q) (w := w) (by omega : 4 ≤ A) hw
      G (S₁.R 132) hfit i
    change |publishedCellRead q w (0 : ZMod s) (S₂.R 132) i-x i| ≤ _
    rw [show S₂.R 132 = cstream A w (chirpLine s G)++S₁.R 132 by simp [S₂]]
    rw [hread]
    exact herror i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
