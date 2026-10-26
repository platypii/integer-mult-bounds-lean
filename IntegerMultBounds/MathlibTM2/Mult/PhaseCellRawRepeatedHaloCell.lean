module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRepeatedBatch
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Gather and execute a generated clipped halo-interior cell on raw RHS replicas.
All geometry comes from the ambient phase scan and the artificial endpoint
cuts. This is the interior pass; boundary/coupling/recovery remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem rawRepeatedHaloCell_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B s t p u target rhsExp a b phase : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B)
    (hphase : phase ∈ haloCellPhases s t (PhaseCellBand.width p u) a b)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u)
      (haloInterior s t (PhaseCellBand.width p u) a b) (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let band := PhaseCellBand.width p u
    let L := haloLength s t band a b phase
    let lo : ZMod s := (haloStart s t band a phase : ℕ)
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let raw := cstream A w (replicaAmbientWords B C)
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L (fun _ => lo) C))
    ∃ v' S' n, v'.user = v.user ∧ n ≤ rawRepeatedBatchCost p l B L s t u target rhsExp lo.val ∧
      Exec body (rawRepeatedBatch hR hQ)
        (mk v (repeatedBatchInputBank (2^15*p) (j+1) q l s t u band L lo.val B
          raw borrowed tail inp out)) n (mk v' S') ∧
      S'.inp = inp ∧ S'.out = out ∧ (∀ k, S'.L k = []) ∧ S'.R 110 = rhs++(raw++borrowed) ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore lo L)
        (publishedBatchRead q w n.val L lo (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys++tail := by
  dsimp only
  let band := PhaseCellBand.width p u
  let L := haloLength s t band a b phase
  let lo : ZMod s := (haloStart s t band a phase : ℕ)
  have hpos : 0 < L := ((mem_haloCellPhases s t band a b phase).mp hphase).2
  obtain ⟨hL,hfit,hint,hcell,hmax⟩ := halo_solver_geometry hst band a b phase hpos
  have hLs : L ≤ s := by omega
  have hpadL : L+L ≤ 2^l+1 := haloLengthKeys_pad hst band a b l hpad L
    (haloLengthKeys_cover hst band a b phase hphase)
  exact rawRepeatedBatch_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
    hB hL hLs hpadL lo C hC (haloInterior s t band a b) x hx hfit hint hcell hmax v tail borrowed inp out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
