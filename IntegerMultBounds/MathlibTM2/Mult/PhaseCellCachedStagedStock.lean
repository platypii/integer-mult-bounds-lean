module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Execute staged arithmetic in the cache bank, counting all spectators once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

theorem cachedStagedCell_sized_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l M L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (v : HS 121 Q A U) (S₀ : Stacks 121 A) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2 ^ 15 * p
    let band := PhaseCellBand.width p u
    let X : ℕ → List GaussianInt := fun _ => columnWords precision s t u band L q (j + 2)
    let Z : ℕ → List GaussianInt := fun _ => reversedColumnWords precision s t u band L q (j + 2)
    let a := reciprocalWord precision s t u band L q (j + 2)
    let source := (List.range M).flatMap (cellSourceRows L lo C)
    let factors := reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))
    let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
    let tailX := csyms A w a ++ (cstream A w (outputWeightWords q (executedOutputTable s t p u M L lo)) ++ payload)
    let S := inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (publishedWords M L (executedOutputWords s t p u q l M L j cExp lo C)) ++ tail)) }
    (embStk weightCacheCoreReg S₀ = S) →
    ∃ v' G m, v'.user = v.user ∧
      m ≤ stagePayloadCost M L w + cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w M L + publishFromDimensionsCost M L w ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S₀) + depth +
        stagedCellWorkspace R K q cExp (8 * p + 1) l w M L)
        depth (embProg weightCacheCoreReg Empty.elim
          (stagedCell (P := Empty) hR hQ)) (mk v S₀) m (mk v' G) ∧
      embStk weightCacheCoreReg G = SF ∧
      ∀ i, 117 ≤ i.val → G.L i = S₀.L i ∧ G.R i = S₀.R i := by
  dsimp only
  intro hinput
  obtain ⟨vi,m,hu,hm,ht⟩ := stagedCell_sized_exec_within
    (body := fun p : Empty => nomatch p) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC
    (embDn weightCacheCoreReg v) tail borrowed inp out R K hpushR hpushK depth
  rw [← hinput] at ht
  obtain ⟨v',G,hv,hu',ht',hproj,hoff⟩ := exec_emb_within_stock
    weightCacheCoreReg weightCacheCoreReg_injective
    (body' := body) (ι := Empty.elim) (fun p => nomatch p) ht v rfl S₀ rfl
  rw [hinput] at hproj
  refine ⟨v',G,m,hu'.trans hu,hm,ht',hproj,?_⟩
  intro i hi
  apply hoff i
  intro k he
  have hk := k.isLt
  have hv := congrArg (fun j : Fin 121 => j.val) he
  dsimp [weightCacheCoreReg] at hv
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
