module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedHaloGroup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchSpecStock

/-! The ambient group geometry instantiates the bounded closed batch specification. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem closedHaloGroup_spec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (J R K : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ K)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' S' m, v'.user = v.user ∧ m ≤ sizedClosedBatchBound p l B L s t u target rhsExp ∧
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
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ S'.R 93 = ys ++ tail := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  have hB : 0 < B := hgroup
  have hgeometry (n : Fin B) := haloGroup_solver_geometry hst band a b L n
  have hLs : L ≤ s := by
    have hh := (hgeometry ⟨0, hB⟩).2.1
    omega
  obtain ⟨v', S', m, huser, hm, he, hrest⟩ := closedBatch_spec_within (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
    (hgeometry ⟨0, hB⟩).1 hLs hpad (haloGroupOrigin s t band a b L) (fun _ => C)
    (fun _ _ k => hC k) (haloInterior s t band a b) (fun _ => x) (fun _ _ => hx)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.2.2) J R K hpushJ hpushR hpushK v tail borrowed inp out
  exact ⟨v', S', m, huser, hm.trans (sizedClosedBatchCost_le_bound p l B L s t u target rhsExp), he, hrest⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
