module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedInputBetween
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloNextInput

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBetweenInputs

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedRecovery

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPreparedReleaseReady

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundaryExtended
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryBuffers

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryUnfold

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 242 Q A U} {body' : P → Pr P 248 Q A U}

theorem packedHaloNextInput_exec (hbody : ∀ f, body' f = embProg packedBoundaryRecoveryBase id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l s t p u target finalTarget rhsExp a b V boundaryTarget : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hα : 0 < α) (hwidth : 8*p ≤ 2^u) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (hab : a ≤ b) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (2*executionPrecision p l target rhsExp+8) t u)
    (hwV : executionWidth p l target rhsExp < 2^V)
    (hcoords : b < 2^V) (hunits : b*executionWidth p l target rhsExp < 2^V)
    (tail : List (Fin (A+4)))
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hsource : S.R 110 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail)

    (haLt : a < s) (hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V)

    (hsep : b-a+PhaseCellBand.width p u ≤ s)

    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hq : executionPrecision p l target rhsExp = executionPrecision p l
      (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
 :
    let band := PhaseCellBand.width p u
    let B := haloBoundary s t band a b
    let bits := boundaryTableBits p boundaryTarget rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    let W := 12*PhaseCellBand.width p u+1
    PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
      q l s t u band a b V w W B.card S →
    ∀ columns : List (ZMod s → GaussianInt),
    PreparedBoundaryColumns A p bits q w W B columns →
    target = boundaryHaloTarget p u boundaryTarget rhsExp B.card →
    (∀ i ∈ B, ∀ j ∈ B, |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-
      (SchurDominance.run (realMatrix s t p u) (haloVertices s a b)
        (haloInterior s t band a b).toList).1 i j| ≤ 1/(2 : ℝ)^bits) →
    let AZ := factorRankIntegerMatrix B W columns
    let K := factorNewtonSteps p q
    let Lc := naturalLineLc q K W B.card AZ
    let Uc := naturalLineUc q K W B.card AZ
    let rcs := naturalLineRcs q K W B.card AZ
    PackedBoundaryFactorPages (cstream A w (Lc.map colC).flatten)
      (cstream A w (Uc.map colC).flatten)
      (cstream A w (rcs.map fun z => (⟨z,0⟩ : GaussianInt))) (embStk packedBoundaryRecoveryBase S) →
    boundaryTarget = boundaryRecoveryTarget p finalTarget →
    ∀ y : ZMod s → ℝ,
    SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) y
      (fun k => (value q (C k)).re) →
    (∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u band (a+j), Fits w z ∧ z.im = 0) →
    ∃ v' F n, ∃ D : ZMod s → GaussianInt,
      v'.user = v.user ∧
      n ≤ packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V ∧
      Exec body' (.seq packedFreshOutput (packedHaloPreparedInput hR hQ)) (mk v S) n (mk v' F) ∧
      F.R 132 = cstream A w (packedInterval a (b-a) D)++S.R 132 ∧
      PhaseCellInterface.ErrorOn (haloVertices s a b)
        (fun i => (packedIntervalRead q w a (F.R 132) i).re) y (1/(2 : ℝ)^finalTarget) ∧
      F.R 110 = tail ∧
      PackedHaloBetweenInputs (2^15*p) (executionStagePrecision p l target rhsExp+1)
        q l s t u band a b V w W B.card F ∧
      (∀ bo hf df, PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase S) →
        PackedBoundaryFactorPages bo hf df (embStk packedBoundaryRecoveryBase F)) ∧
      (∀ k : Fin 242, 168 ≤ k.val → k ≠ 238 →
        (embStk packedBoundaryRecoveryBase F).R k = (embStk packedBoundaryRecoveryBase S).R k) ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k : Fin 168, k ∈ haloAuxiliaryPorts → F.R (packedRecoveryRuntimeReg k) = S.R (packedRecoveryRuntimeReg k)) := by
  dsimp only
  intro hbetween columns hcolumns hcell htable hpages hboundary y hy hcoeff
  let band := PhaseCellBand.width p u
  let B := haloBoundary s t band a b
  let bits := boundaryTableBits p boundaryTarget rhsExp B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let W := 12*band+1
  have hw : executionWidth p l target rhsExp = w := by
    have he := hq; unfold executionPrecision at he
    dsimp [w,bits,B,band,executionWidth]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hbetween₁⟩ := hbetween.allocate_exec (body := body') v S (by omega)
  let S₁ : Stacks 248 A := {S with R := Function.update S.R 132 (cstream A w (List.replicate (b-a) 0)++S.R 132)}
  have hview : embStk packedHaloRuntimeReg (embStk packedBoundaryRecoveryBase S₁) =
      embStk packedRecoveryRuntimeReg S₁ := by rfl
  have hsource₁ : S₁.R 110 = cstream A (executionWidth p l target rhsExp) (packedInterval a (b-a) C)++tail := by
    simpa [S₁] using hsource
  have hpages₁ := hpages
  have hpages₁' : PackedBoundaryFactorPages
      (cstream A w ((naturalLineLc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
      (cstream A w ((naturalLineUc q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map colC).flatten)
      (cstream A w ((naturalLineRcs q (factorNewtonSteps p q) W B.card (factorRankIntegerMatrix B W columns)).map fun z => (⟨z,0⟩ : GaussianInt)))
      (embStk packedBoundaryRecoveryBase S₁) := by
    apply hpages₁.of_solution_frame
    intro k hk hne
    have h132 : packedBoundaryRecoveryBase k ≠ 132 := by
      intro he; have hv := congrArg Fin.val he; change k.val = 132 at hv; omega
    exact Function.update_of_ne h132 _ _
  obtain ⟨v₂,F,n₂,D,hu₂,hn₂,he₂,hout,herror,hsrc,hbetween₂,hpages₂,hsetup₂,hleft₂,hinput₂,houtput₂,hauxiliary₂⟩ :=
    packedHaloPreparedInput_between_exec (body := body) (body' := body') hbody hR hQ hA hp hα hwidth hst hu hαu hθ hgap
      hbudget hpad C hC hab hb hband hwide hVeq hwV hcoords hunits tail
      (cstream A w (List.replicate (b-a) 0)) (S.R 132) v₁ (embStk packedBoundaryRecoveryBase S₁)
      (by rw [hview]; exact hbetween₁.native_bank _ hsource₁)
      (by rw [hview]; simpa only [hq] using hbetween₁.master_copies)
      (by rw [hview]; exact hbetween₁.headers.masters.lower)
      (by rw [hview]; exact hbetween₁.headers.masters.upper)
      (by rw [hview]; exact hbetween₁.headers.geometry)
      (by exact hbetween₁.binaryLength)
      (by simp [embStk,packedHaloRuntimeReg,packedBoundaryRecoveryBase,S₁])
      (by rw [hw]; simp [length_cstream])
      (by intro k hk; rw [hview]; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact hbetween₁.scratch 125 (by decide)
          · exact hbetween₁.scratch 127 (by decide)
          · exact hbetween₁.scratch 130 (by decide)
          · exact hbetween₁.scratch 133 (by decide)
          · exact hbetween₁.scratch 138 (by decide)
          · exact hbetween₁.scratch 129 (by decide)
          · exact hbetween₁.scratch 131 (by decide)
          · exact hbetween₁.scratch 134 (by decide)
          · exact hbetween₁.scratch 135 (by decide)
          · exact hbetween₁.scratch 136 (by decide)
          · exact hbetween₁.scratch 140 (by decide)
          · exact hbetween₁.scratch 153 (by decide)
          · exact hbetween₁.scratch 166 (by decide))
      haLt hfitV (by exact hbetween₁.scratch 139 (by decide)) (by exact hbetween₁.scratch 143 (by decide))
      (by intro k hk; rw [hview]; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl
          all_goals exact hbetween₁.left_low _ (by decide))
      hsep (by exact hbetween₁.scratch 158 (by decide)) (by exact hbetween₁.scratch 167 (by decide))
      (by rw [hw]; exact packedFreshOutput_range _ _ _ _ _) hdom hq
      columns hcolumns hcell htable hbetween₁.bank hpages₁' hboundary y hy hcoeff
  rw [← hbetween₁.eq_extend] at he₂
  refine ⟨v₂,F,n₁+n₂,D,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hout,herror,hsrc,hbetween₂,?_,?_,?_,?_,?_,?_⟩
  · intro bo hf df hpages₀
    apply hpages₂
    apply hpages₀.of_solution_frame
    intro k hk hne
    have h132 : packedBoundaryRecoveryBase k ≠ 132 := by
      intro he; have hv := congrArg Fin.val he; change k.val = 132 at hv; omega
    exact Function.update_of_ne h132 _ _
  · intro k hk hne
    rw [hsetup₂ k hk hne]
    change S₁.R (packedBoundaryRecoveryBase k) = S.R (packedBoundaryRecoveryBase k)
    have h132 : packedBoundaryRecoveryBase k ≠ 132 := by
      intro he
      have hh := congrArg Fin.val he
      change k.val = 132 at hh
      omega
    exact Function.update_of_ne h132 _ _

  · rw [hleft₂]
    rw [← hbetween₁.eq_extend]

  · exact hinput₂
  · exact houtput₂

  · intro k hk
    have hf := hauxiliary₂ k hk
    change F.R (packedRecoveryRuntimeReg k) = S₁.R (packedRecoveryRuntimeReg k) at hf
    apply hf.trans
    apply Function.update_of_ne
    intro he
    have hv := congrArg Fin.val he
    simp only [haloAuxiliaryPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
    change k.val = 132 at hv
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
