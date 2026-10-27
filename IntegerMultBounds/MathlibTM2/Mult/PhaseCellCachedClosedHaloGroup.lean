module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchFromOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets

/-! Execute a nonempty equal-length halo group with retained weights and the closed batch
solver and the original ambient matrix. Raw RHS gathering remains separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

theorem cachedClosedHaloGroup_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 121 Q A U) (S₀ : Stacks 121 A) (tail borrowed cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    (embStk weightCacheCoreReg S₀ = batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedBatchFromOriginsCost p l B L s t u target rhsExp ∧
      Exec body (cachedBatchFromOrigins hR hQ)
        (mk v S₀) m (mk v' S') ∧
      (∀ i, 117 ≤ i.val → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) ∧
      (embStk weightCacheCoreReg S').inp = inp ∧ (embStk weightCacheCoreReg S').out = out ∧ (∀ k, (embStk weightCacheCoreReg S').L k = []) ∧ (embStk weightCacheCoreReg S').R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg S').R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord ((((embStk weightCacheCoreReg S').R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) ((embStk weightCacheCoreReg S').R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ (embStk weightCacheCoreReg S').R 93 = ys ++ tail := by
  dsimp only
  intro hinput hcache hcacheCount h119 h120
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band a b L).length
  have hB : 0 < B := hgroup
  have hgeometry (n : Fin B) := haloGroup_solver_geometry hst band a b L n
  have hLs : L ≤ s := by
    have hh := (hgeometry ⟨0, hB⟩).2.1
    omega
  obtain ⟨v', S', m, huser, hm, he, hrest⟩ := cachedBatchFromOrigins_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget
    (hgeometry ⟨0, hB⟩).1 hLs hpad (haloGroupOrigin s t band a b L) (fun _ => C)
    (fun _ _ k => hC k) (haloInterior s t band a b) (fun _ => x) (fun _ _ => hx)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.2.1)
    (fun n hn => (hgeometry ⟨n, hn⟩).2.2.2.2) v S₀ tail borrowed cacheTail inp out hinput hcache hcacheCount h119 h120
  exact ⟨v', S', m, huser, hm, he, hrest⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
