module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoredRawRepeatedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGroupRHS
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Execute a shared same-origin replica solve, retire its gathered RHS, and
restore the raw source and outer registers while retaining the solved output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem restoredRawRepeatedHaloCell_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B s t p u target rhsExp a b phase : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B)
    (hphase : phase ∈ haloCellPhases s t (PhaseCellBand.width p u) a b)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (v : HS 144 Q A U) (S : Stacks 144 A) (borrowed outTail : List (Fin (A+4)))
    (hbank : embStk groupReg S = repeatedBatchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) (haloLength s t (PhaseCellBand.width p u) a b phase) ((haloStart s t (PhaseCellBand.width p u) a phase : ℕ) : ZMod s).val B
      (cstream A (executionWidth p l target rhsExp) (replicaAmbientWords B C)) borrowed outTail S.inp S.out)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (h128 : (S.R 128).length = (haloLength s t (PhaseCellBand.width p u) a b phase))
    (h130 : (S.R 130).length = executionWidth p l target rhsExp)
    (hfresh : ∀ k ∈ [(131 : Fin 144),134,135,136,137], S.R k = []) :
    let L := haloLength s t (PhaseCellBand.width p u) a b phase
    let lo : ZMod s := (haloStart s t (PhaseCellBand.width p u) a phase : ℕ)
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    ∃ v' S' n, v'.user = v.user ∧ n ≤ restoredRawRepeatedBatchCost p l B L s t u target rhsExp lo.val ∧
      Exec (embTab groupReg body) (restoredRawRepeatedBatch hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (restoredGroupR S.R) 93 (S'.R 93) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore lo L)
        (publishedBatchRead q w n.val L lo (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys++outTail := by
  dsimp only
  let band := PhaseCellBand.width p u
  let L := haloLength s t band a b phase
  let lo : ZMod s := (haloStart s t band a phase : ℕ)
  have hpos : 0 < L := ((mem_haloCellPhases s t band a b phase).mp hphase).2
  obtain ⟨hL,hfit,hint,hcell,hmax⟩ := halo_solver_geometry hst band a b phase hpos
  have hLs : L ≤ s := by omega
  have hpadL : L+L ≤ 2^l+1 := haloLengthKeys_pad hst band a b l hpad L
    (haloLengthKeys_cover hst band a b phase hphase)
  exact restoredRawRepeatedBatch_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
    hB hL hLs hpadL lo C hC (haloInterior s t band a b) x hx hfit hint hcell hmax v S borrowed outTail hbank h129 h133 h128 h130 hfresh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
