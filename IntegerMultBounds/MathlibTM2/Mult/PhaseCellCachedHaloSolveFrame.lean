module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedHaloGroup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedProtectedHaloBatchSolve
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath

/-! Save the generated row count outside the private bank, then execute the
actual closed numerical solver with the ordinary prepared batch ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 148 Q A U}

theorem cachedProtectedHaloBatchSolve_frame_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp a b : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hgroup : 0 < (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length) (hpad : L+L ≤ 2^l+1)
    (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloInterior s t (PhaseCellBand.width p u) a b) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (v : HS 148 Q A U) (S : Stacks 148 A) (borrowed outTail cacheTail : List (Fin (A+4)))
    (hbank : embStk groupReg (embStk cachedGroupLegacyReg S) = batchInputBank (2^15*p) (executionStagePrecision p l target rhsExp+1)
      (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) L
      (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
      (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val)
      (cstream A (executionWidth p l target rhsExp)
        ((List.range (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length).flatMap
          (cellSourceRows L (haloGroupOrigin s t (PhaseCellBand.width p u) a b L) (fun _ => C))))
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) outTail S.inp S.out)
    (h129 : S.R 129 = []) (h133 : S.R 133 = [])
    (hcache : S.R 144 = batchWeightPage A (executionWidth p l target rhsExp)
      (executionPrecision p l target rhsExp) (2^15*p) s t u
      (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length L
      (fun n => (haloGroupOrigin s t (PhaseCellBand.width p u) a b L n).val)++cacheTail)
    (hcacheCount : (S.R 145).length = 2*((haloLengthGroup s t (PhaseCellBand.width p u) a b L).length*
      (L*executionWidth p l target rhsExp))) (h146 : S.R 146 = []) (h147 : S.R 147 = []) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
    let lo := haloGroupOrigin s t (PhaseCellBand.width p u) a b L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo (fun _ => C)))
    ∃ v' S' n, v'.user = v.user ∧ n ≤ (4*B+4)+cachedBatchFromOriginsCost p l B L s t u target rhsExp ∧
      Exec body (cachedProtectedHaloBatchSolve hR hQ) (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      S'.L = S.L ∧
      S'.R 110 = rhs ++ (cstream A w (chirpLine s C) ++ borrowed) ∧
      (∀ k : Fin 148, k.val < 117 → k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      S'.R 129 = List.replicate B tick ∧
      (∀ k : Fin 148, 117 ≤ k.val → k ≠ 129 → S'.R k = S.R k) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) x (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ S'.R 93 = ys ++ outTail := by
  dsimp only
  let B := (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
  obtain ⟨v',T,n,huser,hcost,hexec,hB,hL,hframe,hi,ho,hl,hr,hclean,hpoint,herror,hprefix⟩ :=
    cachedProtectedHaloBatchSolve_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hgroup hpad
      C hC x hx v S outTail
      (cstream A (executionWidth p l target rhsExp) (chirpLine s C)++borrowed) cacheTail S.inp S.out
      (by rw [cachedGroupCore_view]; exact hbank) hcache hcacheCount h146 h147 h129 h133
  refine ⟨v',T,n,huser,hcost,hexec,hi,ho,hL,hr,?_,hB,?_,hpoint,herror,?_⟩
  · intro k hk hk93 hk110
    let j : Fin 117 := ⟨k.val,hk⟩
    have heq : cachedGroupReg (weightCacheCoreReg j) = k := by
      apply Fin.ext
      simp [cachedGroupReg,weightCacheCoreReg,j,hk]
    have h := hclean j
      (by intro he; apply hk93; exact Fin.ext (congrArg (fun i : Fin 117 => i.val) he))
      (by intro he; apply hk110; exact Fin.ext (congrArg (fun i : Fin 117 => i.val) he))
    simpa only [embStk_R,heq] using h
  · intro k hk hk129
    exact (hframe k hk hk129).2
  · obtain ⟨ys,hy,hys⟩ := hprefix
    exact ⟨ys,hy,hys⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
