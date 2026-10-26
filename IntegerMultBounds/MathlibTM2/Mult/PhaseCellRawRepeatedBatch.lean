module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRepeatedClosedBatchSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRepeatedBatchInput

/-! Gather raw same-origin replicas and execute their shared numerical setup.
The raw source and owned gathered RHS remain explicit for later retirement. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def rawRepeatedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq rawReplicaGather (repeatedClosedBatch hR hQ)

def rawRepeatedBatchCost (p l B L s t u target rhsExp lo : ℕ) : ℕ :=
  rawReplicaGatherCost (executionPrecision p l target rhsExp) s lo L (B-1)+
    repeatedClosedBatchCost p l B L s t u target rhsExp lo

theorem rawRepeatedBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) I (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (hfit : lo.val+L ≤ s)
    (hint : ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo+(k : ZMod s)) ∧
      lo+(k : ZMod s) ∈ I)
    (hcell : ∀ k < L, cell s t (lo+(k : ZMod s)) = cell s t lo)
    (hmax : ∀ k ∈ I, cell s t k = cell s t lo → ∃ i < L, lo+(i : ZMod s) = k)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let raw := cstream A w (replicaAmbientWords B C)
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L (fun _ => lo) C))
    ∃ v' S' m, v'.user = v.user ∧ m ≤ rawRepeatedBatchCost p l B L s t u target rhsExp lo.val ∧
      Exec body (rawRepeatedBatch hR hQ)
        (mk v (repeatedBatchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L lo.val B
          raw borrowed tail inp out)) m (mk v' S') ∧
      S'.inp = inp ∧ S'.out = out ∧ (∀ k, S'.L k = []) ∧ S'.R 110 = rhs ++ (raw++borrowed) ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore lo L)
        (publishedBatchRead q w n.val L lo (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys ++ tail := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let raw := cstream A w (replicaAmbientWords B C)
  have hw : 2*q+8 = w := by dsimp [q,w,executionPrecision,executionWidth]; omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := rawRepeatedBatchInput_exec (body := body)
    (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L lo.val B hB hfit C v borrowed tail inp out
  have he₁' := he₁
  simp only [hw,ZMod.natCast_zmod_val] at he₁'
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hrest⟩ := repeatedClosedBatch_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC I x hx hfit hint hcell hmax
    v₁ tail (raw++borrowed) inp out
  exact ⟨v₂,S₂,n₁+n₂,hu₂.trans hu₁,by unfold rawRepeatedBatchCost; dsimp only [q] at *; omega,
    Exec.seq he₁' he₂,hrest⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
