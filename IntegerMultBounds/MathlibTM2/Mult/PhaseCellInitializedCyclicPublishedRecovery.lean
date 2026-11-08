module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalOutputFormat
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalCyclicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicBoundaryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalCyclicBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedBoundaryField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicUnscaledSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundarySolutionAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicBoundaryPageReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicResidualSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSolveTables

/-! Generate and solve the joint cyclic boundary system, then publish its computed real field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def initializedCyclicPublishedRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (initializedCyclicRecovery hR hQ) physicalCyclicPublication

theorem initializedCyclicPublishedRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (has : a < s) (hbs : n ≤ s)
    (rhs : ZMod s → GaussianInt)
    (hrhs : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (rhs i)‖ ≤ (2 : ℝ)^2)
    (v : HS 224 Q A U) (S : Stacks 224 A) (tail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p) (executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2+1)
      (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2
        (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2) (chirpLine s rhs)++tail) (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (haMaster : (S.R 141).length = a) (hnMaster : (S.R 142).length = n)
    (hfresh : ∀ k ∈ [(109 : Fin 224),115,116,144,145,146], S.R k = [])
    (h0 : S.R 0 = [])
    (h139 : S.R 139 = [])
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) (h143 : S.R 143 = []) (h147 : S.R 147 = [])
    (h151 : S.R 151 = []) (h152 : S.R 152 = []) (h153 : S.R 153 = [])
    (hleft : ∀ i : Fin 224, S.L i = []) (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∃ v₀ S₀ m₀ v' S' m, ∃ columns : List (ZMod s → GaussianInt), ∃ G : ZMod s → GaussianInt,
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicRecovery hR hQ)
        (mk v S) m₀ (mk v₀ S₀) ∧
      m ≤ m₀+cyclicPublicationCost (2^15*p) q s t u band a n ∧
      v'.user = v.user ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicPublishedRecovery hR hQ)
        (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R 110 = S.R 110 ∧ S'.R 147 = [] ∧
      S'.R 132 = cstream A w (chirpLine s G)++(bandTableWords A w B (24*band+1) columns 0++S.R 132) ∧
      (∀ i, Fits w (G i)) ∧
      ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun i => (value q (rhs i)).re) →
        PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
          (fun i => (value q (G i)).re) x (1/(2 : ℝ)^target) ∧
        PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
          (fun i => publishedCellRead q w (0 : ZMod s) (S'.R 132) i) x (1/(2 : ℝ)^target) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨va,Sa,ma,vb,Sb,mb,vc,Sc,mc,columns,solution,D,E,hlen,hfits,hprepared,hreadyC,h144,h145,h146,hfreshC,
    hma,hea,hmb,heb,hvc,hmc,hec,hinp,hout,hL,h110,hfield,harchive,haccuracy⟩ := initializedCyclicRecovery_spec
      (body := body) hR hQ hA axis has hbs rhs hrhs v S tail hready haMaster hnMaster hfresh
      h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  let Y := boundarySolutionField B solution
  let G := cyclicPublicationField t band a n D E Y
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hfield' : Sc.R 132 = cstream A (2*q+8) (chirpLine s Y)++
      (bandTableWords A w B (24*band+1) columns 0++S.R 132) := by
    change Sc.R 132 = cstream A w (chirpLine s Y)++_ at hfield
    simpa only [← hw] using hfield
  have harchive' : Sc.R 147 = cstream A (2*q+8) (chirpLine s E)++
      (cstream A (2*q+8) (chirpLine s D)++[]) := by
    change Sc.R 147 = cstream A w (chirpLine s E)++cstream A w (chirpLine s D) at harchive
    simpa only [hw,List.append_nil] using harchive
  obtain ⟨vd,md,hvd,hmd,hed,hreadyD⟩ := physicalCyclicPublication_exec (body := body)
    (P₀ := 2^15*p) (by omega) (axis.hst) has hbs axis.hband D E Y
    (bandTableWords A w B (24*band+1) columns 0++S.R 132) []
    (cstream A w (chirpLine s rhs)++tail) vc Sc hreadyC h144 h145 h146 hfreshC harchive' hfield'
  let F : Stacks 224 A := {Sc with R := (Function.update (Function.update Sc.R 147 []) 132
    (cstream A w (chirpLine s G)++(bandTableWords A w B (24*band+1) columns 0++S.R 132)))}
  have hed' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) physicalCyclicPublication (mk vc Sc) md (mk vd F) := by
    simpa only [F,G,hw] using hed
  have hreal : ∀ i, (G i).im = 0 := fun i => cyclicPublicationField_im t band a n D E Y i
  have hoff : ∀ i ∉ cyclicPrincipalVertices s a n, G i = 0 := by
    apply cyclicPublicationField_off t band a n D E Y
    intro i hi
    apply boundarySolutionField_off B solution i
    intro hj
    exact hi (Finset.mem_sdiff.mp hj).1
  have hacc (x : ZMod s → ℝ)
      (hx : SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
        (fun i => (value q (rhs i)).re)) :
      PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n) (fun i => (value q (G i)).re) x
        (1/(2 : ℝ)^target) := cyclicPublicationField_accuracy q t band a n D E Y x _ (haccuracy x hx)
  have hp : 0 < p := by have := axis.hp; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  obtain ⟨x₀,hx₀⟩ := SchurDominance.solves_exists (realMatrix s t p u) (cyclicPrincipalVertices s a n)
    (1/(8*(p : ℝ))) (by positivity)
    (SchurDominance.dominates_mono _ Finset.univ _ _ (Finset.subset_univ _) axis.hdom)
    (fun i => (value q (rhs i)).re)
  have hone : (1 : ℝ)/(2 : ℝ)^target ≤ 1 :=
    (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hformat := principalOutput_format hp (cyclicPrincipalVertices s a n)
    (execution_stable_output_width p l (initialSchurTarget p u bits 2) 2)
    axis.hdom rhs G hrhs hreal hoff x₀ hx₀ (fun i hi => (hacc x₀ hx₀ i hi).trans hone)
  have hGfits : ∀ i, Fits w (G i) := hformat.2
  refine ⟨vc,Sc,mc,vd,F,mc+md,columns,G,hec,Nat.add_le_add_left hmd mc,hvd.trans hvc,
    Exec.seq hec hed',hinp,hout,hL,?_,by simp [F],by simp [F,w,bits,B,band],hGfits,?_⟩
  · simpa [F] using h110
  · intro x hx
    refine ⟨hacc x hx,?_⟩
    intro i hi
    have hread := publishedCellRead_encodedField (q := q) (by omega : 4 ≤ A)
      (by dsimp [w,executionWidth]; omega : 0 < w) G
      (bandTableWords A w B (24*band+1) columns 0++S.R 132) hGfits i
    change ‖publishedCellRead q w (0 : ZMod s)
      (cstream A w (chirpLine s G)++(bandTableWords A w B (24*band+1) columns 0++S.R 132)) i-x i‖ ≤ _
    rw [hread]
    exact hacc x hx i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
