module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryOutputFields
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedComplexStock

/-! Execute complex pairing directly on certified recovery output. Only the
mathematical identification of component targets remains with the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- Pair precisely the scalar fields encoded by recovery. Output field fits
and scalar accuracy are extracted from the recovery certificate, not supplied. -/
theorem RawRecoveryJob.pair_output_exec (r : RawRecoveryJob s)
    {replicas width count src buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    {word : List (Fin (A+4))} (houtput : r.output word)
    (Zs : List (ZMod s → ℂ))
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) =
      complexComponentTargets Zs)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = Zs.length)
    (hwidth : (S.R width).length = r.problem.span*r.problem.wordWidth)
    (hsrc : S.R src = word++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Zs.length ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ Zs.length*(16*(r.problem.span*r.problem.wordWidth)+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A r.problem.wordWidth
            (packedInterval r.problem.origin r.problem.span D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
        (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
          (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span D)++tail))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs Gs := by
  obtain ⟨E,hword,hgood⟩ := r.output_fields_read hA houtput tail
  let indices := (List.finRange r.problem.Fs.length).reverse
  let Ds := indices.map E
  have hcert : List.Forall₂ (fun y D => PhaseCellInterface.ErrorOn
      (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
      (fun i => (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
        (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span D)++tail) i).re)
      y (1/(2 : ℝ)^r.target)) (complexComponentTargets Zs) Ds := by
    rw [← htargets]
    simp only [Ds,indices,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro j _
    exact (hgood j).2
  have hsrc' : S.R src = (Ds.map (fun D => cstream A r.problem.wordWidth
      (packedInterval r.problem.origin r.problem.span D))).flatten++tail := by
    simpa only [Ds,indices,List.map_map,Function.comp_def] using hsrc.trans (congrArg (fun xs => xs++tail) hword)
  obtain ⟨hlen,v',n,hu,hn,he,herror⟩ := packedComplexBatchAssembly_exec (body := body) hreg hA
    r.problem.precision r.problem.wordWidth r.problem.origin r.problem.span
    (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
    r.problem.span_fit (fun i hi => (PhaseCellDiscreteGeometry.mem_haloVertices _ _ i).mp hi)
    Zs Ds (1/(2 : ℝ)^r.target) tail tail hcert v S hreplicas hwidth hsrc' hcount hbuf hsaved htmp
  exact ⟨_,hlen,v',n,hu,hn,he,herror⟩

/-- The very same pairing run has a linear stock bound over the original
ambient store, independently of the numerical solver's program bodies. -/
theorem pairRecoveryOutput_within_stock
    {replicas width count src buf saved tmp : Fin T}
    {v v' : HS T Q A U} {S G : Stacks T A} {n N W : ℕ}
    (hex : Exec body (pairComplexKey replicas width count src buf saved tmp)
      (Host.mk v S) n (Host.mk v' G)) (hn : n ≤ N*(16*W+9)+14) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*(N*(16*W+9)+14))
      depth (pairComplexKey replicas width count src buf saved tmp)
      (Host.mk v S) n (Host.mk v' G) := by
  have hp : mnNativePushBound 2 (pairComplexKey (P := P) (Q := Q) (A := A) (U := U)
      replicas width count src buf saved tmp) :=
    (packedComplexBatchFinish_pushBound replicas replicas replicas width count src buf saved tmp).1
  exact mn_native_exec_within hex 2 hp depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
