module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchCost
public import IntegerMultBounds.NLogN.PhaseCellLengthGroups

/-! Fully cleaned execution and ambient-core accuracy for a computed equal-length
cell group. Count and origins come from the schedule; generating their
binary origin packets and gathering the raw RHS remain outer execution obligations. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem closedLengthGroup_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hkey : L ∈ lengthKeys s t (PhaseCellBand.width p u)) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (interiorSet s t (PhaseCellBand.width p u)) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (lengthGroup s t (PhaseCellBand.width p u) L).length
    let lo := groupOrigin s t (PhaseCellBand.width p u) L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' S' m, v'.user = v.user ∧ m ≤ sizedClosedBatchBound p l B L s t u target rhsExp ∧
      Exec body (closedBatch hR hQ)
        (mk v (batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B (fun n => (lo n).val)
          rhs borrowed tail inp out)) m (mk v' S') ∧
      S'.inp = inp ∧ S'.out = out ∧ (∀ k, S'.L k = []) ∧ S'.R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys ++ tail := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := (lengthGroup s t band L).length
  have hB : 0 < B := lengthGroup_pos s t band L hkey
  have hgeometry (n : Fin B) := lengthGroup_solver_geometry hst band L n
  have hLs : L ≤ s := by
    have hh := (hgeometry ⟨0, hB⟩).2.1
    omega
  obtain ⟨v', S', m, huser, hm, he, hrest⟩ := closedBatch_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
    (lengthKey_pos hst band L hkey) hLs hpad (groupOrigin s t band L) (fun _ => C)
    (fun _ _ k => hC k) (interiorSet s t band) (fun _ => x) (fun _ _ => hx)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.2.2) v tail borrowed inp out
  rcases hrest with ⟨hi,ho,hl,hr,hclean,hpoint,herror,ys,hylen,hys⟩
  exact ⟨v',S',m,huser,hm.trans (sizedClosedBatchCost_le_bound p l B L s t u target rhsExp),
    he,hi,ho,hl,hr,hclean,hpoint,herror,ys,hylen,hys⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
