module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchivedWindowedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTargetOwnedRecoveryJob
public import IntegerMultBounds.NLogN.PhaseCellCyclicInteriorSplit

/-! Two physical recovery passes share one boundary field and original RHS. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def cyclicRecoveryPasses (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 148 Q A U :=
  .seq (archivedWindowedRecovery hR hQ 144 145) (archivedWindowedRecovery hR hQ 138 146)

def archivedWindowedRecoveryCost (p l s t u target rhsExp boundaryExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  (4*a+4)+((4*b+4)+(recoveryInteriorCoreCost p l s t u target rhsExp boundaryExp
    (couplingCountExponent p u) a b+(2*(a+b)+5)))+
    (archiveResidualPrefixCost q s+retireAmbientSourceCost q s)

theorem cyclicRecoveryPasses_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target rhsExp boundaryExp a n : ℕ} [NeZero s] {alpha gap : ℝ}
    (axis : RecoveryAxisBounds s t p u l alpha gap) (ha : a < s) (hn : n ≤ s)
    (C B : ZMod s → GaussianInt)
    (hB : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i, ‖value (executionPrecision p l
      (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp) (C i)‖ ≤ (2 : ℝ)^boundaryExp)
    (v : HS 148 Q A U) (S : Stacks 148 A) (tail sourceTail : List (Fin (A+4)))
    (hready : LengthKeyReady (2^15*p)
      (executionStagePrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp+1)
      (executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      l s t u (PhaseCellBand.width p u) 0 0
      (cstream A (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
        (chirpLine s B)++tail) (embStk componentReg S))
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a))
    (hfresh : ∀ k ∈ ([(127 : Fin 148),138,141,142,143]), S.R k = [])
    (hsource : S.R 132 = cstream A
      (executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp)
      (chirpLine s C)++sourceTail) :
    let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    let cExp := recoveryRhsExponent p rhsExp boundaryExp (couplingCountExponent p u)
    let R := couplingRowField (2^15*p) q t u band a (a+min n (s-a)) true C B
    let T := couplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true C B
    ∃ v' m, ∃ D E : ZMod s → GaussianInt, ∃ x y : ZMod s → ℝ,
      v'.user = v.user ∧
      m ≤ archivedWindowedRecoveryCost p l s t u target rhsExp boundaryExp a (a+min n (s-a))+
        archivedWindowedRecoveryCost p l s t u target rhsExp boundaryExp 0 (n-min n (s-a)) ∧
      Exec (embTab componentReg (embTab groupReg body)) (cyclicRecoveryPasses hR hQ) (mk v S) m
        (mk v' {S with R := (Function.update S.R 147
          (cstream A w (chirpLine s E)++(cstream A w (chirpLine s D)++S.R 147)))}) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp ∧
        ‖value q (E i)‖ ≤ (2 : ℝ)^interiorOutputExponent p l target cExp) ∧
      SchurDominance.Solves (realMatrix s t p u) (haloInterior s t band a (a+min n (s-a))) x
        (fun i => (value q (R i)).re) ∧
      SchurDominance.Solves (realMatrix s t p u) (haloInterior s t band 0 (n-min n (s-a))) y
        (fun i => (value q (T i)).re) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band a (a+min n (s-a)))
        (fun i => (value q (D i)).re) x (1/(2 : ℝ)^target) ∧
      PhaseCellInterface.ErrorOn (haloInterior s t band 0 (n-min n (s-a)))
        (fun i => (value q (E i)).re) y (1/(2 : ℝ)^target) ∧
      SchurDominance.Solves (realMatrix s t p u) (cyclicPrincipalInterior s t band a n)
        (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then x i else y i)
        (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then (value q (R i)).re else (value q (T i)).re) ∧
      PhaseCellInterface.ErrorOn (cyclicPrincipalInterior s t band a n)
        (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then (value q (D i)).re else (value q (E i)).re)
        (fun i => if i ∈ haloInterior s t band a (a+min n (s-a)) then x i else y i)
        (1/(2 : ℝ)^target) := by
  dsimp only
  let q := executionPrecision p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  let w := executionWidth p l (recoveryFirstTarget p target rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  obtain ⟨v₁,m₁,D,x,hv₁,hm₁,he₁,hRnorm,hDnorm,hx,hDerror⟩ := archivedWindowedRecovery_spec (body := body)
    (a := a) (b := a+min n (s-a)) hR hQ hA 144 145 (by decide)
    axis.hp axis.hpacket axis.hα axis.hst axis.hu axis.hαu axis.hθ axis.hgap axis.hbudget
    axis.hband ha.le (by omega) axis.hpad C B hB (fun i _ => hC i) v S tail sourceTail hready
    haSrc hleftEnd (hfresh 141 (by simp)) (hfresh 142 (by simp)) hsource
    (hfresh 127 (by simp)) (hfresh 138 (by simp)) (hfresh 143 (by simp))
  let F : Stacks 148 A := {S with R := Function.update S.R 147 (cstream A w (chirpLine s D)++S.R 147)}
  have hview : embStk componentReg F = embStk componentReg S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    have hne : componentReg k ≠ (147 : Fin 148) := by
      intro he
      have hv := congrArg (fun j : Fin 148 => j.val) he
      change k.val = 147 at hv
      have := k.isLt
      omega
    simp only [F,embStk,Function.comp_apply,Function.update_of_ne hne]
  have hreadyF := hready
  rw [← hview] at hreadyF
  obtain ⟨v₂,m₂,E,y,hv₂,hm₂,he₂,hTnorm,hEnorm,hy,hEerror⟩ := archivedWindowedRecovery_spec (body := body)
    (a := 0) (b := n-min n (s-a)) hR hQ hA 138 146 (by decide)
    axis.hp axis.hpacket axis.hα axis.hst axis.hu axis.hαu axis.hθ axis.hgap axis.hbudget
    axis.hband (by omega) (by omega) axis.hpad C B hB (fun i _ => hC i) v₁ F tail sourceTail hreadyF
    (by simp [F,hfresh 138 (by simp)]) (by simpa [F] using hrightEnd)
    (by simpa [F] using hfresh 141 (by simp)) (by simpa [F] using hfresh 142 (by simp))
    (by simpa [F] using hsource) (by simpa [F] using hfresh 127 (by simp))
    (by simpa [F] using hfresh 138 (by simp)) (by simpa [F] using hfresh 143 (by simp))
  let band := PhaseCellBand.width p u
  let I := haloInterior s t band a (a+min n (s-a))
  let J := haloInterior s t band 0 (n-min n (s-a))
  have hdisjoint : Disjoint I J := (cyclicPrincipalPieces_disjoint a n ha hn).mono
    (haloInterior_subset s t band a _) (haloInterior_subset s t band 0 _)
  have hnot (i : ZMod s) (hi : i ∈ J) : i ∉ I :=
    fun hj => Finset.disjoint_left.mp hdisjoint hj hi
  have hjoinSolve := cyclicPrincipalInterior_solves (t := t) p u a n ha hn x y
    (fun i => if i ∈ I then
      (value q (couplingRowField (2^15*p) q t u band a (a+min n (s-a)) true C B i)).re else
      (value q (couplingRowField (2^15*p) q t u band 0 (n-min n (s-a)) true C B i)).re)
    (by intro i hi; have hiI : i ∈ I := hi; simpa only [ite_eq_left hiI] using hx i hi)
    (by intro i hi; simpa only [ite_eq_right (hnot i hi)] using hy i hi)
  have hjoinError : PhaseCellInterface.ErrorOn (cyclicPrincipalInterior s t band a n)
      (fun i => if i ∈ I then (value q (D i)).re else (value q (E i)).re)
      (fun i => if i ∈ I then x i else y i) (1/(2 : ℝ)^target) := by
    intro i hi
    by_cases hiI : i ∈ I
    · simpa only [ite_eq_left hiI] using hDerror i hiI
    · have hiJ : i ∈ J := (Finset.mem_union.mp hi).resolve_left hiI
      simpa only [ite_eq_right hiI] using hEerror i hiJ
  refine ⟨v₂,m₁+m₂,D,E,x,y,hv₂.trans hv₁,Nat.add_le_add hm₁ hm₂,
    (Exec.seq he₁ he₂).cast rfl ?_,fun i => ⟨hDnorm i,hEnorm i⟩,hx,hy,hDerror,hEerror,hjoinSolve,hjoinError⟩
  apply congrArg (mk v₂)
  simp [F,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
