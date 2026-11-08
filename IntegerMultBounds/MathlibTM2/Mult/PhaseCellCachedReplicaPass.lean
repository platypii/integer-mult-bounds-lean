module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPassPost

/-! The existing first-pass executor in a composable local contract. Native push
bounds are instantiated at their actual values, rather than supplied by callers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def cachedReplicaPass (job : CachedReplicaPassPlacement T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  initializedCachedReplicaInteriorCoupling job.coupling job.output job.rhs hR hQ

def cachedReplicaPassCost (H : ReplicaHaloProblem s) :=
  (allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
    (placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
      (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (fun L => H.keyCost L+3)).sum+2)))+
    realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+
    releasedRetiredCachedReplicaCouplingCost H

theorem cachedReplicaPass_exec (H : ReplicaHaloProblem s) (job : CachedReplicaPassPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (inputs : CachedReplicaPassInput H job buffers S) :
    ∃ vf F m, ∃ Ds : List (ZMod s → GaussianInt), vf.user = v.user ∧ m ≤ cachedReplicaPassCost H ∧
      Exec body (cachedReplicaPass job hR hQ) (mk v S) m (mk vf F) ∧
      CachedReplicaPassPost H job buffers S F Ds ∧
      ∀ k, ¬job.Owns k → F.L k = S.L k ∧ F.R k = S.R k := by
  let R := mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
    Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR)
  let K := mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
    mul mul_injective (by decide) hQ cr))
  obtain ⟨vf,F,m,Ds,hu,hm,he,hclock,hout₀,hrhs,hready,hmeta,hinp,hout,hgL,hgR,hcache,hsFresh,hnatL,
    hframeL,hframeR,hlen,harch,hgood,hcoeff,hcoeffW,hcoeffRows,hfresh,hformat,haccurate,hnativeR,
    hcleanup,hbankFrame,hretained,hrecRhs⟩ := initializedCachedReplicaInteriorCoupling_exec (body := body)
    H job.coupling job.output job.rhs job.gather_output job.gather_rhs job.bank_output job.bank_rhs
    job.solver_output job.solver_rhs job.output_rhs hR hQ hA hspan horigin R K (le_refl _) (le_refl _) hpad
    buffers v S inputs.headers inputs.bank inputs.cache inputs.solverFresh inputs.input inputs.outputStream
    inputs.savedGather inputs.keys inputs.destination
    (inputs.gatherFresh 86 (by simp)) (inputs.gatherFresh 119 (by simp)) 0 hp hwidth
    inputs.couplingBlank inputs.couplingFresh
    (inputs.couplingWork 136 (by simp)) (inputs.couplingWork 159 (by simp)) (inputs.couplingWork 161 (by simp))
  have hrecWork : ∀ i ∈ [(136 : Fin 168),159,161], F.R (job.coupling.bank i) = [] := by
    intro i hi
    have hlarge : 117 ≤ i.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    have hoff : i ∉ replicaCouplingSetupPorts := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    rw [hbankFrame i hlarge hoff]
    exact inputs.couplingWork i hi
  refine ⟨vf,F,m,Ds,hu,hm,he,⟨hclock,hout₀,hrhs,hready,hmeta,hinp,hout,hgL,hgR,hcache,hsFresh,hnatL,
    hlen,harch,hgood,hcoeff,hcoeffW,hcoeffRows,hfresh,hformat,haccurate,hnativeR,hcleanup,hbankFrame,hretained,hrecRhs,hrecWork⟩,?_⟩
  intro k hk
  have off {N : ℕ} (f : Fin N → Fin T) (howns : ∀ i, job.Owns (f i)) : ∀ i, f i ≠ k := by
    intro i hi
    apply hk
    rw [← hi]
    exact howns i
  have ho : job.output ≠ k := by intro hi; apply hk; rw [← hi]; exact .output
  have hr : job.rhs ≠ k := by intro hi; apply hk; rw [← hi]; exact .rhs
  exact ⟨hframeL k (off _ (fun i => .gather i)) (off _ (fun i => .solver i)) ho,
    hframeR k (off _ (fun i => .bank i)) (off _ (fun i => .gather i)) (off _ (fun i => .solver i)) ho hr⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
