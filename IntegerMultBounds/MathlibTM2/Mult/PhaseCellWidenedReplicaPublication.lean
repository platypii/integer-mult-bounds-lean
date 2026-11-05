module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenedPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaPublication

/-! Convert one complete replica archive once, then run the existing restoring
replica sweep. Only the source and ambient destination change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
variable {T Q A s L : ℕ} {P U : Type} {src dst : Fin T}

theorem widenedReplicaPublication_exec (body : P → Pr P T Q A U)
    (plan : PreparedPublicationPlan T src dst) (clock lineRows : Fin T)
    (hports : (plan.support++[src,dst,clock,lineRows]).Nodup)
    (wide width count work saved tmp extra : Fin T)
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (windows : PublicationWindows s L) (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (xs : List GaussianInt) (replicas : List (PublicationReplica A))
    (hvalid : ∀ r ∈ replicas, r.Valid windows W 0)
    (hencoded : replicas.flatMap (PublicationReplica.input W) = cstream A W (xs.map (symZ w)))
    (sourceTail outputTail borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : plan.Ready windows W 0 borrowed S)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hcount : (S.R count).length = xs.length*w)
    (hsrc : S.R src = cstream A w xs++sourceTail)
    (hdst : S.R dst = replicas.flatMap PublicationReplica.ambient++outputTail)
    (hclock : (S.R clock).length = replicas.length) (hline : (S.R lineRows).length = s)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ widenPackedPrefixCost w W xs.length+
        (replicaPublicationCost replicas.length s 0 L W+37*s*W+6*replicas.length+31) ∧
      Exec body (.seq (widenPackedPrefix wide width count src work saved tmp extra)
        (plan.replicaProgram clock lineRows)) (mk v S) n (mk v' F) ∧
      F.R src = sourceTail ∧ F.R dst = replicas.flatMap (PublicationReplica.output windows W)++outputTail ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ≠ dst → F.R i = S.R i := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := widenEncodedPrefix_exec (body := body) hreg w W hw hwidth
    xs sourceTail v S hwide hword hcount hsrc hblank
  let M : Stacks T A := {S with R := Function.update S.R src (cstream A W (xs.map (symZ w))++sourceTail)}
  have hr : plan.Ready windows W 0 borrowed M := hready.of_frame (by
    intro i hi
    exact Function.update_of_ne (plan.support_off hi).1 _ _)
  have htail := (List.nodup_append.mp hports).2.1
  have hc : clock ≠ src := by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false] at htail; tauto
  have hlr : lineRows ≠ src := by simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false] at htail; tauto
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hi,ho,hl,hframe⟩ := plan.replica_exec (body := body)
    clock lineRows hports windows W 0 (hw.trans hwidth) replicas hvalid
    sourceTail outputTail borrowed v₁ M hr
    (by simp only [M,Function.update_self,hencoded])
    (by simpa only [M,Function.update_of_ne plan.src_ne_dst.symm] using hdst)
    (by simpa only [M,Function.update_of_ne hc] using hclock)
    (by simpa only [M,Function.update_of_ne hlr] using hline)
  refine ⟨v₂,F,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,hs,hd,hi,ho,hl,?_⟩
  intro i his hid
  exact (hframe i his hid).trans (Function.update_of_ne his _ _)


open IntegerMultBounds.MathlibTM2.Fast.Main

theorem widenedReplicaPublication_within (body : P → Pr P T Q A U)
    (plan : PreparedPublicationPlan T src dst) (clock lineRows wide width count work saved tmp extra : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n bill depth : ℕ)
    (he : Exec body (.seq (widenPackedPrefix wide width count src work saved tmp extra)
      (plan.replicaProgram clock lineRows)) (mk v S) n (mk v' F)) (hn : n ≤ bill) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*bill) depth
      (.seq (widenPackedPrefix wide width count src work saved tmp extra)
        (plan.replicaProgram clock lineRows)) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 13
    ⟨widenPackedPrefix_native _ _ _ _ _ _ _ _,
      mnNativePushBound_mono (by decide) (plan.replica_native clock lineRows)⟩ depth _ (by omega)

/-- Charge one common-width pass by encoded volume, independently of the
coefficient witnesses and narrow word width. -/
theorem widenPackedPrefixCost_le_volume (w W coefficients : ℕ)
    (hW : 1 ≤ W) (hw : w ≤ W) :
    widenPackedPrefixCost w W coefficients ≤ 40*(coefficients+1)*W := by
  have hstep : 6*w+10*W+10 ≤ 26*W := by omega
  have hmul := Nat.mul_le_mul_left coefficients hstep
  have hsub : W-w ≤ W := Nat.sub_le _ _
  unfold widenPackedPrefixCost
  nlinarith

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
