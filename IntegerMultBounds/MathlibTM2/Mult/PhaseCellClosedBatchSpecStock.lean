module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchExecStock

/-! Retain the existing closed batch accuracy contract on its bounded cleaned trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem closedBatch_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) I (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (hfit : ∀ n < B, (lo n).val+L ≤ s)
    (hint : ∀ n < B, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo n+(k : ZMod s)) ∧
      lo n+(k : ZMod s) ∈ I)
    (hcell : ∀ n < B, ∀ k < L, cell s t (lo n+(k : ZMod s)) = cell s t (lo n))
    (hmax : ∀ n < B, ∀ k ∈ I, cell s t k = cell s t (lo n) → ∃ i < L, lo n+(i : ZMod s) = k)
    (J R K : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ K)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
    ∃ v' S' m, v'.user = v.user ∧ m ≤ sizedClosedBatchCost p l B L s t u target rhsExp ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize
          (mk v (batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B (fun n => (lo n).val)
            rhs borrowed tail inp out))+depth+sizedClosedBatchWorkspace J R K p l B L s t u target rhsExp)
        depth (closedBatch hR hQ)
        (mk v (batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B (fun n => (lo n).val)
          rhs borrowed tail inp out)) m (mk v' S')) ∧
      S'.inp = inp ∧ S'.out = out ∧ (∀ k, S'.L k = []) ∧ S'.R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ S'.R 93 = ys ++ tail := by
  dsimp only
  obtain ⟨v',S',m,huser,hm,he,hpost⟩ := closedBatch_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC I x hx hfit hint hcell hmax
    v tail borrowed inp out
  obtain ⟨vf,nf,_,_,hf,_⟩ := closedBatch_sized_exec_within (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC
    J R K hpushJ hpushR hpushK v tail borrowed inp out
  obtain ⟨heqn,heqF⟩ := (hf 0).toExec.unique he
  rw [heqn,heqF] at hf
  exact ⟨v',S',m,huser,hm,hf,hpost⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
