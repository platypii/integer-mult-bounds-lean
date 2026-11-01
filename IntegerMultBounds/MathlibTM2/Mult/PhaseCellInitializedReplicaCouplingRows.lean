module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingCursor

/-! Finish an actual initialized interior trace with real projection and aligned
RHS queue construction. The resulting cursor supplies physical coupling rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def initializedReplicaCouplingRows (plan : ReplicaInteriorPlacement T) (output rhs : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (realInitializedReplicaHaloLoop plan output hR hQ) (prepareReplicaCouplingRows plan rhs)

theorem initializedReplicaCouplingRows_finish (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (output rhs : Fin T)
    (houtput : ∀ k, plan.gather k ≠ output) (hrhs : ∀ k, plan.gather k ≠ rhs) (hsep : output ≠ rhs)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 4 ≤ A) (buffers : ReplicaLoopBuffers A)
    (v v₀ : HS T Q A U) (S F : Stacks T A) (n depth W : ℕ)
    (hu₀ : v₀.user = v.user)
    (he₀ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+W) depth
      (initializedReplicaHaloLoop plan output hR hQ) (mk v S) n (mk v₀ F))
    (h : ReplicaHaloLoopState H plan output buffers (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F)
    (hdom : SchurDominance.DominatesOn (realMatrix s H.t H.p H.u) Finset.univ (1/(8*(H.p : ℝ)))) :
    ∃ v' G m, v'.user = v.user ∧
      m ≤ n+realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (W+2*realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth))) depth
        (initializedReplicaCouplingRows plan output rhs hR hQ) (mk v S) m (mk v' G) ∧
      ReplicaCouplingCursor H output rhs buffers.accumulatorTail (F.R rhs) 0 G ∧
      embStk plan.gather G = embStk plan.gather F ∧
      G.L = F.L ∧ G.inp = F.inp ∧ G.out = F.out ∧
      (∀ k, k ≠ output → k ≠ rhs → G.R k = F.R k) := by
  obtain ⟨v₁,J,n₁,hu₁,hn₁,he₁,hfields,hgather₁,hleft₁,hi₁,ho₁,hframe₁⟩ :=
    realReplicaHaloOutput_exec_within (body := body) H plan output houtput hA buffers v₀ F h hdom depth
  have headers : ReplicaLoopHeaders H plan.gather buffers J := by
    apply h.headers.of_frame
    intro k _ _
    exact congrFun (congrArg Stacks.R hgather₁) k
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hrows,hgather₂,hleft,hi,ho,hframe⟩ :=
    prepareReplicaCouplingRows_exec_within (body := body) H plan output rhs hrhs hsep buffers v₁ J headers hfields depth
  have hrhsFrame : J.R rhs = F.R rhs := hframe₁ rhs hsep.symm
  refine ⟨v₂,G,(n+n₁)+n₂,hu₂.trans (hu₁.trans hu₀),by omega,?_,?_,hgather₂.trans hgather₁,
    hleft.trans hleft₁,hi.trans hi₁,ho.trans ho₁,?_⟩
  · have hsize₀ := he₀.final
    have hsize₁ := he₁.final
    refine .seq (.seq (he₀.mono ?_) (he₁.mono ?_)) (he₂.mono ?_)
    all_goals intro d z hz; omega
  · rw [← hrhsFrame]
    exact ReplicaCouplingRows.cursor H output rhs buffers.accumulatorTail (J.R rhs) G hrows

  · intro k houtput hrhs
    exact (hframe k hrhs).trans (hframe₁ k houtput)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
