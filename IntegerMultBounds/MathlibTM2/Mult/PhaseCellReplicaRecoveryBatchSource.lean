module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows

/-! The preparation archive has reverse source order. Reuse the existing
restoring row scan to install the second-pass source, with its actual bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem ReplicaHaloProblem.source_exec_within (H : ReplicaHaloProblem s)
    (Fs : List (ZMod s → GaussianInt)) (hcountRows : Fs.length = H.Fs.length)
    (count savedCount volume source archive dst saved tmp : Fin T)
    (hreg : [count,savedCount,volume,source,archive,dst,saved,tmp].Nodup)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = H.Fs.length) (hvolume : (S.R volume).length = H.span*H.wordWidth)
    (hsource : S.R source = Fs.reverse.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++borrowed)
    (hfresh : ∀ k ∈ [savedCount,archive,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)) depth
        (reverseCopyRows count savedCount volume source archive dst saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R dst (Fs.flatMap
          (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++S.R dst)}) := by
  let rows := Fs.reverse.map (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))
  have hlen : ∀ row ∈ rows, row.length = H.span*H.wordWidth := by
    intro row hrow
    obtain ⟨R,_,rfl⟩ := List.mem_map.mp hrow
    simp only [length_cstream,packedInterval_length _ H.span_fit]
  obtain ⟨v',n,hu,hn,he⟩ := reverseCopyRows_exec_within (body := body)
    count savedCount volume source archive dst saved tmp hreg (H.span*H.wordWidth) rows hlen borrowed v S
    (by simpa only [rows,List.length_map,List.length_reverse,hcountRows] using hcount)
    hvolume (by simpa only [rows,List.flatMap_def] using hsource) hfresh depth
  refine ⟨v',n,hu,?_,?_⟩
  · simpa only [rows,List.length_map,List.length_reverse,hcountRows] using hn
  · simpa only [rows,List.length_map,List.length_reverse,hcountRows,←List.map_reverse,
      List.reverse_reverse,List.flatMap_def] using he

theorem ReplicaHaloProblem.source_headers_exec_within (H J : ReplicaHaloProblem s)
    (layout : H.SameLayout J)
    (gather : Fin 126 → Fin T) (hinj : Function.Injective gather) (source : Fin T)
    (hsep : ∀ k, gather k ≠ source) (buffers : ReplicaLoopBuffers A)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H gather buffers S)
    (hsource : S.R source = J.Fs.reverse.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++borrowed) (depth : ℕ) :
    let F := {S with R := Function.update S.R (gather 124) (J.Fs.flatMap
      (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++S.R (gather 124))}
    let nextBuffers := {buffers with packedRhsTail := S.R (gather 124), savedGather := embStk gather F}
    ∃ v' n, v'.user = v.user ∧ n ≤ reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)) depth
        (reverseCopyRows (gather 121) (gather 89) (gather 123) source (gather 88)
          (gather 124) (gather 104) (gather 105)) (Host.mk v S) n (Host.mk v' F) ∧
      ReplicaLoopHeaders J gather nextBuffers F := by
  dsimp only
  let F := {S with R := Function.update S.R (gather 124) (J.Fs.flatMap
    (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++S.R (gather 124))}
  have hreg : [gather 121,gather 89,gather 123,source,gather 88,gather 124,gather 104,gather 105].Nodup := by
    simp [List.nodup_cons,hsep,Ne.symm (hsep _),hinj.eq_iff]
  obtain ⟨v',n,hu,hn,he⟩ := H.source_exec_within (body := body) J.Fs layout.count
    (gather 121) (gather 89) (gather 123) source (gather 88) (gather 124) (gather 104) (gather 105)
    hreg borrowed v S
    (by simpa [replicaFactoryHeaderValue] using
      headers.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide))
    headers.volume hsource
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact headers.fresh _ (by simp)) depth
  refine ⟨v',n,hu,hn,he,?_⟩
  apply headers.replace_source layout gather buffers _ S F
  · intro k hk
    exact Function.update_of_ne (hinj.ne hk) _ _
  · simpa only [layout.wordWidth,layout.origin,layout.span,F,Function.update_self]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
