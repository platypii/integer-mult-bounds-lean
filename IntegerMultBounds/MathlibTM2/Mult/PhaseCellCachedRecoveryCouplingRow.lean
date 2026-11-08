module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedReplicaRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingBounds

/-! Recovery rows share one coefficient page, selector pair and numerical bank.
Only the original RHS queue and the computed RHS archive advance per coupling. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type} {body : Empty → Pr Empty 168 Q A U}

structure CachedRecoveryCouplingReady (H : ReplicaHaloProblem s)
    (raw pageTail : List (Fin (A+4))) (S : Stacks 168 A) : Prop where
  ready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
    H.origin (H.origin+H.span) raw (embStk groupReg (embStk intervalPageReg S))
  page : S.R 138 = cstream A H.wordWidth (couplingCoefficientPageInterval
    (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++pageTail
  rows : (S.R 140).length = 2*H.band+1
  words : (S.R 139).length = (couplingCoefficientPageInterval
    (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length
  count : S.R 165 = binSyms H.metadataWidth H.span
  ribbon : S.R 159 = (couplingRibbonFlags (s := s) true H.t H.band H.origin
    (H.origin+H.span) H.origin H.span).map (fun flag => pairSym A flag flag)
  guard : S.R 161 = recoveryGuardIntervalSymbols true A s H.t (2*H.band)
    H.origin (H.origin+H.span) H.origin H.span
  fresh : ∀ i ∈ [(127 : Fin 168),143,166,158,135,167], S.R i = []

def cachedRecoveryCouplingState (S : Stacks 168 A)
    (rhsTail output : List (Fin (A+4))) : Stacks 168 A :=
  {S with R := (Function.update (Function.update S.R 93 rhsTail) 110 (output++S.R 110))}

theorem CachedRecoveryCouplingReady.feed {H : ReplicaHaloProblem s}
    {raw pageTail : List (Fin (A+4))} {S : Stacks 168 A}
    (h : CachedRecoveryCouplingReady H raw pageTail S)
    (rhsTail output : List (Fin (A+4))) :
    CachedRecoveryCouplingReady H (output++raw) pageTail
      (cachedRecoveryCouplingState S rhsTail output) := by
  refine ⟨h.ready.feed_frame rhsTail output,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [cachedRecoveryCouplingState] using h.page
  · simpa [cachedRecoveryCouplingState] using h.rows
  · simpa [cachedRecoveryCouplingState] using h.words
  · simpa [cachedRecoveryCouplingState] using h.count
  · simpa [cachedRecoveryCouplingState] using h.ribbon
  · simpa [cachedRecoveryCouplingState] using h.guard
  · intro i hi
    have hn : i ≠ (93 : Fin 168) ∧ i ≠ 110 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [cachedRecoveryCouplingState,hn.1,hn.2] using h.fresh i hi

/-- Advancing the boundary queue leaves the shared recovery cache intact. -/
theorem CachedRecoveryCouplingReady.update_source {H : ReplicaHaloProblem s}
    {raw pageTail : List (Fin (A+4))} {S : Stacks 168 A}
    (h : CachedRecoveryCouplingReady H raw pageTail S) (tail : List (Fin (A+4))) :
    CachedRecoveryCouplingReady H raw pageTail {S with R := Function.update S.R 132 tail} := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [intervalPageCore_updateR S 132 (by decide)]
    exact h.ready
  · simpa using h.page
  · simpa using h.rows
  · simpa using h.words
  · simpa using h.count
  · simpa using h.ribbon
  · simpa using h.guard
  · intro i hi
    have hn : i ≠ (132 : Fin 168) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [hn] using h.fresh i hi

def cachedRecoveryCouplingRowCost (H : ReplicaHaloProblem s) : ℕ :=
  let N := H.span; let w := H.wordWidth; let band := H.band; let V := H.metadataWidth
  (((16*N*w+21*N+14*band*w+13*band+11*V+46)+cachedGatheredRibbonCost (N+2*band) w+
    (12*((N+2*band)*w)+11*(N+2*band)+14))+(12*((N+2*band)*w)+17*N+26*band+11*V+24)+
    ((6*N+6)+(6*N+11*V+6+(retainedPageSpatialIntervalLoopCost true H.precision w s H.t band
      H.origin (H.origin+N) H.origin N+(22*N+22*V+22+transferCountedLineCost N w+
        transferCountedLineCost (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u band
          H.origin (H.origin+N) H.origin N).length w)))))+(28*N*w+36*N+11*V+26)

noncomputable def cachedRecoveryCouplingWorkspace (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) : ℕ :=
  let K := mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr)
  cachedLocalCouplingWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) K H.precision H.wordWidth
    s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth+
    mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U))*
      (28*H.span*H.wordWidth+36*H.span+11*H.metadataWidth+26)

theorem cachedRecoveryCouplingRow_exec_within (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsep : H.span+H.band ≤ s)
    (C B : ZMod s → GaussianInt) (hC : ∀ j, Fits H.wordWidth (C j))
    (tail rhsTail raw pageTail : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (cache : CachedRecoveryCouplingReady H raw pageTail S)
    (hsource : S.R 132 = cstream A H.wordWidth (packedInterval H.origin H.span C)++tail)
    (hrhs : S.R 93 = cstream A H.wordWidth (packedInterval H.origin H.span B)++rhsTail) :
    let output := cstream A H.wordWidth (packedInterval H.origin H.span
      (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
        H.origin (H.origin+H.span) true C B))
    ∃ vf m, vf.user = v.user ∧ m ≤ cachedRecoveryCouplingRowCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          cachedRecoveryCouplingWorkspace (A := A) (U := U) H hQ)
        depth (cachedLocalFeedCouplingInterval hQ) (mk v S) m
          (mk vf (cachedRecoveryCouplingState S rhsTail output))) ∧
      CachedRecoveryCouplingReady H (output++raw) pageTail
        (cachedRecoveryCouplingState S rhsTail output) := by
  dsimp only
  have hw5 : 5 ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.wordWidth executionWidth
    omega
  have hqw : H.precision+4 ≤ H.wordWidth := by
    have hc := H.coupling_coefficient_width
    have hp := H.p_pos
    omega
  obtain ⟨vf,m,hu,hm,he⟩ := cachedLocalFeedCouplingInterval_exec_within (body := body)
    hQ true hA hw5 hqw H.s_lt_t C B H.span_fit tail pageTail rhsTail raw
    _ (le_refl _) v S cache.ready rfl rfl hsep hsource (cache.fresh 127 (by simp))
    cache.rows cache.page hrhs (cache.fresh 143 (by simp)) hC
    (fun j _ => H.coupling_coefficients (H.origin+j)) H.metadataWidth H.metadataWidth_fits.2.1
    cache.count (cache.fresh 166 (by simp)) cache.words H.span_fit H.band_fit
    cache.ribbon cache.guard (cache.fresh 158 (by simp)) (cache.fresh 135 (by simp))
    (cache.fresh 167 (by simp))
  exact ⟨vf,m,hu,hm,he,cache.feed rhsTail _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
