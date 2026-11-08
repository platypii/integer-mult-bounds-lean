module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCyclicPublishedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicSlice
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

noncomputable def initializedCyclicCroppedRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 224 Q A U :=
  .seq (initializedCyclicPublishedRecovery hR hQ) preparedCyclicSlice

theorem initializedCyclicCroppedRecovery_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicPublishedRecovery hR hQ)
        (mk v S) m₀ (mk v₀ S₀) ∧
      m ≤ m₀+preparedCyclicSliceCost q s a n ∧ v'.user = v.user ∧
      Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
        (embTab componentReg (embTab groupReg body))))) (initializedCyclicCroppedRecovery hR hQ)
        (mk v S) m (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R 110 = S.R 110 ∧
      S'.R 132 = cstream A w (chirpLine s G)++(bandTableWords A w B (24*band+1) columns 0++S.R 132) ∧
      S'.R 147 = cstream A w (cyclicInterval a n G) ∧ (S'.R 147).length = n*w ∧
      (∀ i, (G i).im = 0) ∧ (∀ i, Fits w (G i)) ∧
      ∀ x : ZMod s → ℝ,
        SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalVertices s a n) x
          (fun i => (value q (rhs i)).re) →
        PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
          (fun i => (cyclicIntervalRead q w a (S'.R 147) i).re) x (1/(2 : ℝ)^target) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  obtain ⟨va,Sa,ma,vb,Sb,mb,columns,G,hea,hmb,hvb,heb,hinp,hout,hL,h110,h147,hfield,
    hreadyB,h144,h145,h146,hq,hfreshB,hreal,hfits,haccuracy⟩ := initializedCyclicPublishedRecovery_spec
      (body := body) hR hQ hA axis has hbs rhs hrhs v S tail hready haMaster hnMaster hfresh
      h0 h139 h127 h138 h143 h147 h151 h152 h153 hleft hnew
  have hw : w = 2*q+8 := by dsimp [w,q,executionWidth,executionPrecision]; omega
  have hsource : Sb.R 132 = cstream A (2*q+8) (chirpLine s G)++
      (bandTableWords A w B (24*band+1) columns 0++S.R 132) := by
    change Sb.R 132 = cstream A w (chirpLine s G)++_ at hfield
    simpa only [← hw] using hfield
  obtain ⟨vc,mc,hvc,hmc,hec⟩ := preparedCyclicSlice_exec
    (body := embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) q a n has hbs G
    (bandTableWords A w B (24*band+1) columns 0++S.R 132) vb Sb hq h144 h145 h146 hfreshB hsource
  let F : Stacks 224 A := {Sb with R := Function.update Sb.R 147 (cstream A w (cyclicInterval a n G))}
  have hec' : Exec (embTab boundaryFactorLegacyReg (embTab tableReg (embTab boundaryArithmeticReg
      (embTab componentReg (embTab groupReg body))))) preparedCyclicSlice (mk vb Sb) mc (mk vc F) := by
    simpa only [F,hw,h147,List.append_nil] using hec
  refine ⟨vb,Sb,mb,vc,F,mb+mc,columns,G,heb,Nat.add_le_add_left hmc mb,hvc.trans hvb,
    Exec.seq heb hec',hinp,hout,hL,?_,?_,?_,?_,hreal,hfits,?_⟩
  · simpa [F] using h110
  · simpa [F] using hfield
  · simp [F,w,bits,B,band]
  · simp [F,w,bits,B,band]
  · intro x hx
    have h := cyclicIntervalRead_error (A := A) q w a n (by omega) (by dsimp [w,executionWidth]; omega)
      has G hfits [] x (1/(2 : ℝ)^target) (haccuracy x hx).1
    change PhaseCellInterface.ErrorOn (cyclicPrincipalVertices s a n)
      (fun i => (cyclicIntervalRead q w a (cstream A w (cyclicInterval a n G)) i).re) x _
    simpa only [List.append_nil] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
