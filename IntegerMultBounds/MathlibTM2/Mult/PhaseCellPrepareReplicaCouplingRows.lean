module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaHaloOutput

/-! Preserve the original RHS and create a row queue in the solver's actual
reverse replica order. The projected output is already in that same order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReplicaCouplingRows (plan : ReplicaInteriorPlacement T) (rhs : Fin T) : Pr P T Q A U :=
  reverseCopyRows (plan.gather 121) (plan.gather 89) (plan.gather 123) (plan.gather 124)
    (plan.gather 88) rhs (plan.gather 104) (plan.gather 105)

structure ReplicaCouplingRows (H : ReplicaHaloProblem s) (output rhs : Fin T)
    (outputTail rhsTail : List (Fin (A+4))) (S : Stacks T A) : Prop where
  output : RealReplicaHaloOutput H output outputTail S
  rhs : S.R rhs = H.Fs.reverse.flatMap (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))++rhsTail

theorem prepareReplicaCouplingRows_exec_within (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (output rhs : Fin T)
    (hgd : ∀ k, plan.gather k ≠ rhs) (hsep : output ≠ rhs)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H plan.gather buffers S)
    (hout : RealReplicaHaloOutput H output buffers.accumulatorTail S) (depth : ℕ) :
    ∃ v' G n, v'.user = v.user ∧ n ≤ reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)) depth
        (prepareReplicaCouplingRows plan rhs) (mk v S) n (mk v' G) ∧
      ReplicaCouplingRows H output rhs buffers.accumulatorTail (S.R rhs) G ∧
      embStk plan.gather G = embStk plan.gather S ∧ G.L = S.L ∧ G.inp = S.inp ∧ G.out = S.out ∧
      (∀ k, k ≠ rhs → G.R k = S.R k) := by
  let rows := H.Fs.map (fun F => cstream A H.wordWidth (packedInterval H.origin H.span F))
  have hlen : ∀ row ∈ rows, row.length = H.span*H.wordWidth := by
    intro row hrow
    obtain ⟨F,hF,rfl⟩ := List.mem_map.mp hrow
    simp [length_cstream,packedInterval_length F H.span_fit]
  have hregs : [plan.gather 121,plan.gather 89,plan.gather 123,plan.gather 124,
      plan.gather 88,rhs,plan.gather 104,plan.gather 105].Nodup := by
    simp [List.nodup_cons,hgd,Ne.symm (hgd _),plan.gather_injective.eq_iff]
  have hN : (S.R (plan.gather 121)).length = rows.length := by
    simpa [rows,replicaFactoryHeaderValue] using headers.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  obtain ⟨v',n,hu,hn,he⟩ := reverseCopyRows_exec_within (body := body)
    (plan.gather 121) (plan.gather 89) (plan.gather 123) (plan.gather 124)
    (plan.gather 88) rhs (plan.gather 104) (plan.gather 105) hregs
    (H.span*H.wordWidth) rows hlen buffers.packedRhsTail v S hN headers.volume
    (by simpa only [rows,List.flatMap_def] using headers.source)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact headers.fresh _ (by simp)) depth
  let G : Stacks T A := {S with R := Function.update S.R rhs (rows.reverse.flatten++S.R rhs)}
  refine ⟨v',G,n,hu,by simpa only [rows,List.length_map] using hn,?_,?_,?_,rfl,rfl,rfl,?_⟩
  · simpa only [rows,List.length_map,prepareReplicaCouplingRows] using he
  · refine ⟨?_,?_⟩
    · obtain ⟨fields,hlen,hfields,hgood⟩ := hout
      exact ⟨fields,hlen,by simpa [G,hsep] using hfields,hgood⟩
    · simp [G,rows,List.map_reverse,List.flatMap_def]
  · exact embStk_updateR_off S rhs _ hgd
  · intro k hk
    simp [G,hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
