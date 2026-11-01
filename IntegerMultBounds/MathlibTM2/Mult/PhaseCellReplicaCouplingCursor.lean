module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReplicaCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStageReplicaCouplingRow

/-! The physical paired row queues advance together. Each staged coupling input
carries the matching original RHS, stable real field and original error target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def ReplicaHaloRowSpec (H : ReplicaHaloProblem s) (r : ℕ) (D : ZMod s → GaussianInt) : Prop :=
  (∀ i, (D i).im = 0) ∧ (∀ i, Fits H.wordWidth (D i)) ∧
    (∀ i ∈ haloInterior s H.t H.band H.origin (H.origin+H.span),
      ‖value H.precision (D i)‖ ≤ (2 : ℝ)^stableInteriorExponent H.p H.rhsExp) ∧
    PhaseCellInterface.ErrorOn (haloInterior s H.t H.band H.origin (H.origin+H.span))
      (fun i => (value H.precision (D i)).re) (H.x r) (1/(2 : ℝ)^H.target)

structure ReplicaCouplingCursor (H : ReplicaHaloProblem s) (output rhs : Fin T)
    (outputTail rhsTail : List (Fin (A+4))) (r : ℕ) (S : Stacks T A) : Prop where
  index : r ≤ H.Fs.length
  output : ∃ fields : List (ZMod s → GaussianInt), fields.length = H.Fs.length-r ∧
    S.R output = (fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++outputTail ∧
    ∀ j : Fin fields.length, ReplicaHaloRowSpec H (r+j.val) fields[j.val]
  rhs : S.R rhs = (H.Fs.reverse.drop r).flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail

theorem ReplicaCouplingRows.cursor (H : ReplicaHaloProblem s) (output rhs : Fin T)
    (outputTail rhsTail : List (Fin (A+4))) (S : Stacks T A)
    (h : ReplicaCouplingRows H output rhs outputTail rhsTail S) :
    ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S := by
  obtain ⟨fields,hlen,hout,hgood⟩ := h.output
  exact ⟨Nat.zero_le _,⟨fields,by simpa using hlen,hout,by simpa only [ReplicaHaloRowSpec,Nat.zero_add] using hgood⟩,
    by simpa only [List.drop_zero] using h.rhs⟩

theorem ReplicaCouplingCursor.of_frame (H : ReplicaHaloProblem s) (output rhs : Fin T)
    (outputTail rhsTail : List (Fin (A+4))) (r : ℕ) (S G : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail r S)
    (hout : G.R output = S.R output) (hrhs : G.R rhs = S.R rhs) :
    ReplicaCouplingCursor H output rhs outputTail rhsTail r G := by
  obtain ⟨fields,hlen,hfields,hgood⟩ := h.output
  exact ⟨h.index,⟨fields,hlen,hout.trans hfields,hgood⟩,hrhs.trans h.rhs⟩

theorem ReplicaCouplingCursor.finished (H : ReplicaHaloProblem s) (output rhs : Fin T)
    (outputTail rhsTail : List (Fin (A+4))) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail H.Fs.length S) :
    S.R output = outputTail ∧ S.R rhs = rhsTail := by
  obtain ⟨fields,hlen,hfields,hgood⟩ := h.output
  have hf : fields = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
  refine ⟨by simpa only [hf,List.map_nil,List.flatten_nil,List.nil_append] using hfields,?_⟩
  have hd : H.Fs.reverse.drop H.Fs.length = [] := List.drop_eq_nil_of_le (by simp)
  simpa only [hd,List.flatMap_nil,List.nil_append] using h.rhs

theorem ReplicaCouplingCursor.stage (H : ReplicaHaloProblem s)
    (volume output rhs fieldDst rhsDst saved tmp : Fin T)
    (hreg : [volume,output,rhs,fieldDst,rhsDst,saved,tmp].Nodup)
    (outputTail rhsTail : List (Fin (A+4))) (r : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail r S) (hr : r < H.Fs.length)
    (hV : (S.R volume).length = H.span*H.wordWidth) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ C R : ZMod s → GaussianInt, ∃ v' G, v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*stageReplicaCouplingRowCost (H.span*H.wordWidth)) depth
        (stageReplicaCouplingRow volume output rhs fieldDst rhsDst saved tmp) (Host.mk v S)
        (stageReplicaCouplingRowCost (H.span*H.wordWidth)) (Host.mk v' G) ∧
      ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) G ∧
      G.R fieldDst = cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R fieldDst ∧
      G.R rhsDst = cstream A H.wordWidth (packedInterval H.origin H.span R)++S.R rhsDst ∧
      ReplicaHaloRowSpec H r C ∧ R = H.Fs.reverse.getD r (fun _ => 0) ∧
      (∀ i, ‖value H.precision (R i)‖ ≤ (2 : ℝ)^H.rhsExp) ∧
      (∀ k, k ∉ [output,rhs,fieldDst,rhsDst] → G.R k = S.R k) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨fields,hlen,houtput,hgood⟩ := h.output
  have hne : fields ≠ [] := by
    intro hz
    rw [hz,List.length_nil] at hlen
    omega
  obtain ⟨C,fields,rfl⟩ := List.exists_cons_of_ne_nil hne
  have hri : r < H.Fs.reverse.length := by simpa using hr
  let R := H.Fs.reverse[r]
  have hdrop := List.drop_eq_getElem_cons hri
  have hC : ReplicaHaloRowSpec H r C := by simpa only [Nat.add_zero,List.getElem_cons_zero] using hgood ⟨0,by simp⟩
  have hfield : S.R output = cstream A H.wordWidth (packedInterval H.origin H.span C)++
      ((fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++outputTail) := by
    simpa only [List.map_cons,List.flatten_cons,List.append_assoc] using houtput
  have hrhs : S.R rhs = cstream A H.wordWidth (packedInterval H.origin H.span R)++
      ((H.Fs.reverse.drop (r+1)).flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail) := by
    rw [h.rhs,hdrop,List.flatMap_cons,List.append_assoc]
  obtain ⟨v',hu,he⟩ := stageReplicaCouplingRow_exec_within (body := body)
    volume output rhs fieldDst rhsDst saved tmp hreg (H.span*H.wordWidth)
    (cstream A H.wordWidth (packedInterval H.origin H.span C))
    (cstream A H.wordWidth (packedInterval H.origin H.span R))
    ((fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++outputTail)
    ((H.Fs.reverse.drop (r+1)).flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail)
    (by simp [length_cstream,packedInterval_length C H.span_fit])
    (by simp [length_cstream,packedInterval_length R H.span_fit]) v S hV hfield hrhs hsaved htmp depth
  let G : Stacks T A := {S with R := (Function.update (Function.update (Function.update (Function.update S.R output
    ((fields.map (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D))).flatten++outputTail))
    fieldDst (cstream A H.wordWidth (packedInterval H.origin H.span C)++S.R fieldDst)) rhs
    ((H.Fs.reverse.drop (r+1)).flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail))
    rhsDst (cstream A H.wordWidth (packedInterval H.origin H.span R)++S.R rhsDst))}
  have hR : R = H.Fs.reverse.getD r (fun _ => 0) := by rw [List.getD_eq_getElem _ _ hri]
  refine ⟨C,R,v',G,hu,he,?_,?_,?_,hC,hR,?_,?_⟩
  · refine ⟨by omega,⟨fields,by simp only [List.length_cons] at hlen; omega,?_,?_⟩,?_⟩
    · simp [G,‹output ≠ rhsDst›,‹output ≠ rhs›,‹output ≠ fieldDst›]
    · intro j
      have hj : j.val+1 < (C::fields).length := by have hh := j.isLt; simp only [List.length_cons]; omega
      have hh := hgood ⟨j.val+1,hj⟩
      simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    · simp [G,‹rhs ≠ rhsDst›]
  · simp [G,‹fieldDst ≠ rhsDst›,‹rhs ≠ fieldDst›.symm]
  · simp [G]
  · rw [hR]
    exact H.rhs_bound r hr
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    simp [G,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
