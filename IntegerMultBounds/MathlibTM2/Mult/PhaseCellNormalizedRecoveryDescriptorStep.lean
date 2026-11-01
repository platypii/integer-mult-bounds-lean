module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedGeneratedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryDescriptorStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBankStepStock
public import IntegerMultBounds.MathlibTM2.StackInvariantShift

/-! Raw input descriptors execute normalization before the complete physical
cached caller, then collect output and restore both sides of the private bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def normalizedRecoveryDescriptorStep (work : Fin 392 → Fin T)
    (src saved count tmp spare result : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  descriptorBankStep work src saved count tmp spare result 391 (normalizedGeneratedRecovery hR hQ)

theorem normalizedRecoveryDescriptorStep_exec (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt))
    (hfields : H.Fs = recoveryInputFields H.p H.precision Fs)
    (hpq : H.p+1 ≤ H.precision) (hW : H.wordWidth ≤ W) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (target : ℕ)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (time stock : ℕ)
    (hbudget : ∀ B : ReplicaRecoveryBatch H target X,
      normalizeRecoveryInputCost H W Fs.length+generatedReplicaBoundaryFactoryCost H target+firstCachedReplicaRecoveryTime H (B.problem htarget) ≤ time ∧
      registerBankStock (rawRecoveryInput (A := A) H W Fs [] [])+
        (normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*normalizeRecoveryInputCost H W Fs.length+
          generatedRecoveryInputStock H [] []+
        generatedFirstCachedReplicaRecoveryWorkspace H (B.problem htarget) target hR hQ push c M R K) ≤ stock)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T) (hreg : [src,saved,count,tmp,spare,result].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result])
    (v : HS T Q A U) (S : Stacks T A) (rest : List (Fin (A+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hsource : S.R src = descriptorBankTape (placedDescriptorFields work (rawRecoveryInput (A := A) H W Fs [] []).R)++rest)
    (hcount : S.R count = []) (htmp : S.R tmp = []) (hspare : S.R spare = []) :
    ∃ v' n output, v'.user = v.user ∧
      n ≤ takeDescriptorBankCost (placedDescriptorFields work (rawRecoveryInput (A := A) H W Fs [] []).R)+time+(6*stock+2358) ∧
      Exec body (normalizedRecoveryDescriptorStep work src saved count tmp spare result hR hQ) (mk v S) n
        (mk v' (dispatchedDescriptorState work (rawRecoveryInput (A := A) H W Fs [] []).R src saved result rest output S)) ∧
      GeneratedRecoveryOutput H target X output ∧
      ∀ C, mnProgPush (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
          work src saved count tmp spare result hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work (rawRecoveryInput (A := A) H W Fs [] []).R)+stock+(6*stock+2358)))
          depth (normalizedRecoveryDescriptorStep work src saved count tmp spare result hR hQ) (mk v S) n
          (mk v' (dispatchedDescriptorState work (rawRecoveryInput (A := A) H W Fs [] []).R src saved result rest output S)) := by
  let words := (rawRecoveryInput (A := A) H W Fs [] []).R
  let solve : Pr Empty 392 Q A U := normalizedGeneratedRecovery hR hQ
  let post : Stacks 392 A → Prop := fun F => F.inp = S.inp ∧ F.out = S.out ∧
    GeneratedRecoveryOutput H target X (F.R 391) ∧ registerBankStock F ≤ stock
  have hready : descriptorReadyBank work words S = rawRecoveryInput H W Fs S.inp S.out := by
    refine Stacks.ext rfl rfl ?_ rfl
    funext i
    exact hleft i
  have hsolve : ∀ vi : HS 392 Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words S)) n (mk vf F) ∧ post F ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words S))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words S)) n (mk vf F) := by
    intro vi
    obtain ⟨B,Ds,vf,F,n,outputs,hlen,hu,hn,hcert,h257,h247,h391,he,hstreams⟩ :=
      normalizedGeneratedRecovery_exec_within H W Fs hfields hpq hW hR hQ hA hspan horigin
        R K hpushR hpushK hpad S.inp S.out vi 0 hp hwidth target push c hpush M hpushM X hX htarget
    have hb := (hbudget B).2
    have hraw : mnSize (mk vi (rawRecoveryInput (A := A) H W Fs S.inp S.out)) =
        S.inp.length+S.out.length+registerBankStock (rawRecoveryInput (A := A) H W Fs [] []) := by
      rw [mnSize_mk_registerBankStock]
      rfl
    have hsize := he.final
    rw [mnSize_mk_registerBankStock,hstreams.1,hstreams.2,hraw] at hsize
    have hbank : registerBankStock F ≤ stock := by omega
    refine ⟨vf,F,n,hu,hn.trans (hbudget B).1,?_,⟨hstreams.1,hstreams.2,⟨B,Ds,outputs,hlen,hcert,h391⟩,hbank⟩,?_⟩
    · rw [hready]
      exact he.toExec
    · intro C _ depth
      have hscale : stock ≤ (C+1)*stock := Nat.le_mul_of_pos_left _ (by omega)
      have ht := mn_exec_within_shift he depth
      simp only [Nat.zero_add] at ht
      rw [hready]
      apply ht.mono
      intro d z hz
      omega
  exact descriptorBankStep_exec_stock (body := body) work hwork src saved count tmp spare result hreg hsep
    words rest 391 solve time stock (GeneratedRecoveryOutput H target X) v S
    hblank hleft hsource hcount htmp hspare hsolve

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
