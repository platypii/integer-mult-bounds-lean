module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaHaloLoop

/-! Finish the executed interior pass with paid real projection. Its actual
packed output has fitting real fields and precision-independent solve bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def realReplicaHaloOutput (plan : ReplicaInteriorPlacement T) (dst : Fin T) : Pr P T Q A U :=
  realReplicaRows (plan.gather 121) (plan.gather 123) dst
    (plan.gather 88) (plan.gather 89) (plan.gather 104)

def RealReplicaHaloOutput (H : ReplicaHaloProblem s) (dst : Fin T)
    (tail : List (Fin (A+4))) (G : Stacks T A) : Prop :=
  ∃ fields : List (ZMod s → GaussianInt), fields.length = H.Fs.length ∧
    G.R dst = (fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++tail ∧
    ∀ r : Fin fields.length, (∀ i, (fields[r.val] i).im = 0) ∧ (∀ i, Fits H.wordWidth (fields[r.val] i)) ∧
      (∀ i ∈ haloInterior s H.t H.band H.origin (H.origin+H.span),
        ‖value H.precision (fields[r.val] i)‖ ≤ (2 : ℝ)^stableInteriorExponent H.p H.rhsExp) ∧
      PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
        (fun i => (value H.precision (fields[r.val] i)).re) (H.x r.val) (1/(2 : ℝ)^H.target)

theorem realReplicaHaloOutput_exec_within (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (dst : Fin T) (hgd : ∀ k, plan.gather k ≠ dst)
    (hA : 4 ≤ A) (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (F : Stacks T A)
    (h : ReplicaHaloLoopState H plan dst buffers (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F)
    (hdom : SchurDominance.DominatesOn (realMatrix s H.t H.p H.u) Finset.univ (1/(8*(H.p : ℝ))))
    (depth : ℕ) :
    ∃ v' G n, v'.user = v.user ∧ n ≤ realReplicaRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        2*realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)) depth
        (realReplicaHaloOutput plan dst) (mk v F) n (mk v' G) ∧
      RealReplicaHaloOutput H dst buffers.accumulatorTail G ∧
      embStk plan.gather G = embStk plan.gather F ∧ G.L = F.L ∧ G.inp = F.inp ∧ G.out = F.out ∧
      (∀ k, k ≠ dst → G.R k = F.R k) := by
  obtain ⟨fields,hlen,hout,hgood,haccuracy⟩ := ReplicaHaloLoopState.packedFields H plan dst buffers F hA h
  let xs := (fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten
  have hxs : xs.length = H.Fs.length*(H.span*H.wordWidth) := by
    have hh := length_flatten_const (L := H.span*H.wordWidth)
      (fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))) (by
        intro row hrow
        obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hrow
        simp [length_cstream,packedInterval_length D H.span_fit])
    simpa only [List.length_map,hlen] using hh
  have hregs : [plan.gather 121,plan.gather 123,dst,plan.gather 88,plan.gather 89,plan.gather 104].Nodup := by
    simp [List.nodup_cons,hgd,Ne.symm (hgd _),plan.gather_injective.eq_iff]
  have hN : (F.R (plan.gather 121)).length = H.Fs.length := by
    simpa [replicaFactoryHeaderValue] using h.headers.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  obtain ⟨v',n,hu,hn,he⟩ := realReplicaRows_exec_within (body := body)
    (plan.gather 121) (plan.gather 123) dst (plan.gather 88) (plan.gather 89) (plan.gather 104)
    hregs H.Fs.length (H.span*H.wordWidth) v F xs buffers.accumulatorTail hN h.headers.volume hout hxs
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact h.headers.fresh _ (by simp)) depth
  let G : Stacks T A := {F with R := Function.update F.R dst (xs.map realPartSymbol++buffers.accumulatorTail)}
  let realFields := fields.map (fun D i => realPartWord (D i))
  have hstable := H.realFields_stable hdom fields hlen haccuracy
  refine ⟨v',G,n,hu,hn,he,?_,?_,rfl,rfl,rfl,?_⟩
  · refine ⟨realFields,by simp [realFields,hlen],?_,?_⟩
    · simp only [G,Function.update_self]
      dsimp only [xs]
      rw [packedReplicaFields_real hA]
      simp only [realFields,List.map_map]
      rfl
    · intro r
      have hr : r.val < fields.length := by simpa [realFields] using r.isLt
      simp only [realFields,List.getElem_map]
      refine ⟨fun _ => rfl,?_,?_,?_⟩
      · intro i
        apply fits_of_value_power (interiorOutput_width H.p H.l H.target H.rhsExp)
        rw [value_realPartWord_norm]
        exact (Complex.abs_re_le_norm _).trans ((hgood _ (List.getElem_mem hr)).1 i)
      · exact hstable ⟨r.val,hr⟩
      · simpa only [value_realPartWord_re] using haccuracy ⟨r.val,hr⟩
  · exact embStk_updateR_off F dst _ hgd
  · intro k hk
    simp [G,hk]

noncomputable def realInitializedReplicaHaloLoop (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (initializedReplicaHaloLoop plan dst hR hQ) (realReplicaHaloOutput plan dst)

/-- Append the proved projection to any actual initialized-pass trace. -/
theorem realInitializedReplicaHaloLoop_finish (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (dst : Fin T) (hgd : ∀ k, plan.gather k ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 4 ≤ A) (buffers : ReplicaLoopBuffers A)
    (v v₁ : HS T Q A U) (S F : Stacks T A) (n depth W : ℕ)
    (hu₁ : v₁.user = v.user)
    (he₁ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+W) depth
      (initializedReplicaHaloLoop plan dst hR hQ) (mk v S) n (mk v₁ F))
    (h : ReplicaHaloLoopState H plan dst buffers (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F)
    (hdom : SchurDominance.DominatesOn (realMatrix s H.t H.p H.u) Finset.univ (1/(8*(H.p : ℝ)))) :
    ∃ v' G m, v'.user = v.user ∧ m ≤ n+realReplicaRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (W+2*realReplicaRowsCost H.Fs.length (H.span*H.wordWidth))) depth
        (realInitializedReplicaHaloLoop plan dst hR hQ) (mk v S) m (mk v' G) ∧
      RealReplicaHaloOutput H dst buffers.accumulatorTail G ∧ embStk plan.gather G = embStk plan.gather F := by
  obtain ⟨v',G,m,hu,hm,he,hfields,hgather,_⟩ := realReplicaHaloOutput_exec_within (body := body)
    H plan dst hgd hA buffers v₁ F h hdom depth
  refine ⟨v',G,n+m,hu.trans hu₁,by omega,?_,hfields,hgather⟩
  have hsize := he₁.final
  refine .seq (he₁.mono ?_) (he.mono ?_)
  all_goals intro d z hz; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
