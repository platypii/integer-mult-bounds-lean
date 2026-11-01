module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPackedPublicationMerge
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem

/-! Select one actual second-pass row with its retained boundary row. The
existing recovery contract proves the physically archived field's final error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem ReplicaRecoveryBatch.assemble_row_exec {H : ReplicaHaloProblem s} {target : ℕ}
    {X : ℕ → ZMod s → ℝ} (B : ReplicaRecoveryBatch H target X) (htarget)
    (r : Fin H.Fs.length) (D : ZMod s → GaussianInt)
    (hD : ReplicaHaloRowSpec (B.problem htarget) r.val D)
    (master count width mask x y reversed dst trash tmp : Fin T)
    (hreg : [master,count,width,mask,x,y,reversed,dst,trash,tmp].Nodup)
    (hA : 4 ≤ A) (tailX tailY : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hmaster : S.R master = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span)
    (hwidth : (S.R width).length = H.wordWidth)
    (hX : S.R x = cstream A H.wordWidth (packedInterval H.origin H.span D)++tailX)
    (hY : S.R y = cstream A H.wordWidth (packedInterval H.origin H.span (B.boundary r))++tailY)
    (hcount : S.R count = []) (hmask : S.R mask = [])
    (hreversed : S.R reversed = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) (depth : ℕ) :
    let E := B.recoveredField r D
    (∀ i, Fits H.wordWidth (E i)) ∧
    PhaseCellInterface.ErrorOn (haloVertices s H.origin (H.origin+H.span))
      (fun i => (value H.precision (E i)).re) (X r.val) (1/(2 : ℝ)^target) ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedPackedPublicationMergeCost H.span H.wordWidth ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*retainedPackedPublicationMergeCost H.span H.wordWidth) depth
        (retainedPackedPublicationMerge master count width mask x y reversed dst trash tmp)
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R x tailX)
          y tailY) dst (cstream A H.wordWidth (packedInterval H.origin H.span E)++S.R dst))}) := by
  obtain ⟨hfits,herror⟩ := B.accept_row htarget r D hD
  refine ⟨hfits,herror,?_⟩
  obtain ⟨v',n,hu,hn,he⟩ := retainedPackedPublicationMerge_exec (body := body)
    (band := H.band) master count width mask x y reversed dst trash tmp hreg hA H.s_lt_t H.span_fit
    D (B.boundary r) tailX tailY v S hmaster hwidth hX hY hcount hmask hreversed htrash htmp
  refine ⟨v',n,hu,hn,?_⟩
  exact mn_native_exec_within he 2
    (retainedPackedPublicationMerge_native master count width mask x y reversed dst trash tmp) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn) _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
