module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRecoveryPairWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairRecoveryOutput
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Pair certified scalar recovery output from retained numerical masters,
including packet-header generation and retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def preparedPairRecoveryOutput (e : Fin 8 → Fin T) (replicas count src buf : Fin T) : Pr P T Q A U :=
  .seq (embProg e Empty.elim prepareRecoveryPairWidth)
    (.seq (pairComplexKey replicas (e 5) count src buf (e 7) (e 6)) (uclear (e 5)))

noncomputable def preparedPairRecoveryOutputCost (r : RawRecoveryJob s) (N : ℕ) : ℕ :=
  prepareRecoveryPairWidthCost r.problem.precision r.problem.origin (r.problem.origin+r.problem.span)+
    (N*(16*(r.problem.span*r.problem.wordWidth)+9)+14)+(2*(r.problem.span*r.problem.wordWidth)+2)

theorem RawRecoveryJob.prepared_pair_output_exec (r : RawRecoveryJob s)
    (e : Fin 8 → Fin T) (he : Function.Injective e) (replicas count src buf : Fin T)
    (hreg : [replicas,e 5,count,src,buf,e 7,e 6].Nodup) (hA : 4 ≤ A)
    {word : List (Fin (A+4))} (houtput : r.output word) (Zs : List (ZMod s → ℂ))
    (htargets : (List.finRange r.problem.Fs.length).reverse.map (fun j => r.solution j.val) = complexComponentTargets Zs)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R (e 0)).length = r.problem.precision)
    (ha : (S.R (e 1)).length = r.problem.origin)
    (hb : (S.R (e 2)).length = r.problem.origin+r.problem.span)
    (hblank : ∀ k ∈ ([(3 : Fin 8),4,5,6,7]), S.R (e k) = [])
    (hreplicas : (S.R replicas).length = Zs.length) (hsrc : S.R src = word++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) :
    ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Zs.length ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ preparedPairRecoveryOutputCost r Zs.length ∧
      Exec body (preparedPairRecoveryOutput e replicas count src buf) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A r.problem.wordWidth
            (packedInterval r.problem.origin r.problem.span D))).flatten++tail))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
        (PhaseCellDiscreteGeometry.haloVertices s r.problem.origin (r.problem.origin+r.problem.span))
        (packedIntervalRead r.problem.precision r.problem.wordWidth r.problem.origin
          (cstream A r.problem.wordWidth (packedInterval r.problem.origin r.problem.span D)++tail))
        z (1/(2 : ℝ)^r.target+1/(2 : ℝ)^r.target)) Zs Gs := by
  have hr := hreg
  regs_ne hr
  have hw : 2*r.problem.precision+8 = r.problem.wordWidth := by
    unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionPrecision executionWidth
    omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,_⟩ := placedPrepareRecoveryPairWidth_exec (body' := body) e he
    r.problem.precision r.problem.origin (r.problem.origin+r.problem.span) v S hq ha hb hblank
  rw [Nat.add_sub_cancel_left,hw] at he₁
  let F : Stacks T A := {S with R := (Function.update S.R (e 5)
    (List.replicate (r.problem.span*r.problem.wordWidth) tick))}
  have hframe (k : Fin T) (hk : k ≠ e 5) : F.R k = S.R k := Function.update_of_ne hk _ _
  obtain ⟨Gs,hlen,v₂,n₂,hu₂,hn₂,he₂,hgood⟩ := r.pair_output_exec hreg hA houtput Zs htargets tail v₁ F
    (by rw [hframe _ ‹replicas ≠ e 5›]; exact hreplicas)
    (by simp [F]) (by rw [hframe _ ‹e 5 ≠ src›.symm]; exact hsrc)
    (by rw [hframe _ ‹e 5 ≠ count›.symm]; exact hcount)
    (by rw [hframe _ ‹e 5 ≠ buf›.symm]; exact hbuf)
    (by rw [hframe _ ‹e 5 ≠ e 7›.symm]; exact hblank 7 (by simp))
    (by rw [hframe _ ‹e 5 ≠ e 6›.symm]; exact hblank 6 (by simp))
  let output := (Gs.map (fun D => cstream A r.problem.wordWidth
    (packedInterval r.problem.origin r.problem.span D))).flatten++tail
  let G : Stacks T A := {F with R := Function.update F.R src output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (e 5) v₂ G
  have hpacket : (G.R (e 5)).length = r.problem.span*r.problem.wordWidth := by
    simp [G,F,‹e 5 ≠ src›]
  have hfinal : {G with R := Function.update G.R (e 5) []} = {S with R := Function.update S.R src output} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = e 5
    · subst k; simp [‹e 5 ≠ src›,hblank 5 (by simp)]
    · simp [G,F,Function.update_apply,hk]
  rw [hpacket,hfinal] at he₃
  refine ⟨Gs,hlen,v₃,n₁+(n₂+(2*(r.problem.span*r.problem.wordWidth)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁ (Exec.seq he₂ he₃),hgood⟩
  unfold preparedPairRecoveryOutputCost
  omega

theorem preparedPairRecoveryOutput_native (e : Fin 8 → Fin T) (replicas count src buf : Fin T) :
    mnNativePushBound 8 (preparedPairRecoveryOutput (P := P) (Q := Q) (A := A) (U := U)
      e replicas count src buf) := by
  refine ⟨embProg_native e Empty.elim _ prepareRecoveryPairWidth_native,?_,?_⟩
  · exact mnNativePushBound_mono (by decide : 2 ≤ 8)
      (packedComplexBatchFinish_pushBound replicas replicas replicas (e 5) count src buf (e 7) (e 6)).1
  · simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

/-- Setup, complex pairing and packet-header retirement share one local-volume
stock bound over the actual ambient initial state. -/
theorem preparedPairRecoveryOutput_within_stock
    {e : Fin 8 → Fin T} {replicas count src buf : Fin T}
    {v v' : HS T Q A U} {S G : Stacks T A} {n : ℕ} {r : RawRecoveryJob s} {N : ℕ}
    (hex : Exec body (preparedPairRecoveryOutput e replicas count src buf) (Host.mk v S) n (Host.mk v' G))
    (hn : n ≤ preparedPairRecoveryOutputCost r N) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      8*preparedPairRecoveryOutputCost r N) depth (preparedPairRecoveryOutput e replicas count src buf)
      (Host.mk v S) n (Host.mk v' G) :=
  mn_native_exec_within hex 8 (preparedPairRecoveryOutput_native e replicas count src buf) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
