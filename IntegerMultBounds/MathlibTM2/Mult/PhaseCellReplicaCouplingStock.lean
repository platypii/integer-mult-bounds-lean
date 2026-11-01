module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingCursor
public import IntegerMultBounds.MathlibTM2.Host.ReplaceThreeStock

/-! One coupling transition consumes two queued rows and archives one row.
Its completed stock decreases, independently of numerical execution details. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {s T Q A : ℕ} [NeZero s] {U : Type}

omit [NeZero s] in
theorem ReplicaCouplingCursor.queue_lengths (H : ReplicaHaloProblem s) (output rhs : Fin T)
    (outputTail rhsTail : List (Fin (A+4))) (r : ℕ) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail r S) :
    (S.R output).length = (H.Fs.length-r)*(H.span*H.wordWidth)+outputTail.length ∧
      (S.R rhs).length = (H.Fs.length-r)*(H.span*H.wordWidth)+rhsTail.length := by
  obtain ⟨fields,hlen,hfields,_⟩ := h.output
  constructor
  · simp [hfields,List.length_flatten,List.map_map,Function.comp_def,packedInterval_length _ H.span_fit,
      List.map_const',List.sum_replicate,smul_eq_mul,hlen]
  · simp [h.rhs,List.length_flatMap,packedInterval_length _ H.span_fit,
      List.map_const',List.sum_replicate,smul_eq_mul]

theorem ReplicaCouplingCursor.stock_le (H : ReplicaHaloProblem s) (output rhs dst : Fin T)
    (hreg : [output,rhs,dst].Nodup) (outputTail rhsTail : List (Fin (A+4))) (r : ℕ)
    (v w : HS T Q A U) (S F : Stacks T A)
    (hS : ReplicaCouplingCursor H output rhs outputTail rhsTail r S)
    (hF : ReplicaCouplingCursor H output rhs outputTail rhsTail (r+1) F) (hr : r < H.Fs.length)
    (hL : F.L = S.L) (hi : F.inp = S.inp) (ho : F.out = S.out)
    (hframe : ∀ k, k ∉ [output,rhs,dst] → F.R k = S.R k)
    (harchive : (F.R dst).length = (S.R dst).length+H.span*H.wordWidth) :
    mnSize (Host.mk w F) ≤ mnSize (Host.mk v S) := by
  have hregs := hreg
  regs_ne hregs
  have hstate : F = {S with R := (Function.update (Function.update (Function.update S.R output (F.R output))
      rhs (F.R rhs)) dst (F.R dst))} := by
    refine Stacks.ext hi ho hL ?_
    funext k
    by_cases hkout : k = output <;> by_cases hkrhs : k = rhs <;> by_cases hkdst : k = dst
    all_goals first
      | (subst k; simp [‹output ≠ rhs›,‹output ≠ dst›,‹rhs ≠ dst›])
      | (simp [hkout,hkrhs,hkdst,hframe k (by simp [hkout,hkrhs,hkdst])])
  have hstock := mn_replace_three_size output rhs dst (by assumption) (by assumption) (by assumption)
    v w S (F.R output) (F.R rhs) (F.R dst)
  rw [←hstate] at hstock
  obtain ⟨hoS,hrS⟩ := ReplicaCouplingCursor.queue_lengths H output rhs outputTail rhsTail r S hS
  obtain ⟨hoF,hrF⟩ := ReplicaCouplingCursor.queue_lengths H output rhs outputTail rhsTail (r+1) F hF
  have hcount : H.Fs.length-r = H.Fs.length-(r+1)+1 := by omega
  rw [hcount,Nat.add_mul,one_mul] at hoS hrS
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
