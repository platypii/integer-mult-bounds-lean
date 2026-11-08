module

public import IntegerMultBounds.MathlibTM2.Routing.HaloWindowCounts
public import IntegerMultBounds.MathlibTM2.Routing.HaloWindowStep
public import IntegerMultBounds.MathlibTM2.NativePushBoundMono
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! A complete metadata-driven monotone window: decode its varying counts,
emit once, and retire both counters for the next window. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloWindowRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloWindowCounts HaloWindowStep
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readEmitWindow (width queue binary duplicate work bodyCount keepCount src archive oldOverlap nextOverlap saved tmp : Fin T) : Pr P T Q A U :=
  .seq (readCounts width nextOverlap queue binary bodyCount keepCount duplicate work saved tmp)
    (.seq (emitWindow bodyCount keepCount src archive oldOverlap nextOverlap saved tmp)
      (clearWords [bodyCount,keepCount]))

theorem readEmitWindow_native
    (width queue binary duplicate work bodyCount keepCount src archive oldOverlap nextOverlap saved tmp : Fin T) :
    mnNativePushBound 3 (readEmitWindow (P := P) (Q := Q) (A := A) (U := U)
      width queue binary duplicate work bodyCount keepCount src archive oldOverlap nextOverlap saved tmp) :=
  ⟨readCounts_native _ _ _ _ _ _ _ _ _ _,
    mnNativePushBound_mono (by omega) (emitWindow_pushBound _ _ _ _ _ _ _ _),
    mnNativePushBound_mono (by omega) (clearWords_native _)⟩

theorem readEmitWindow_exec
    (width queue binary duplicate work bodyCount keepCount src archive oldOverlap nextOverlap saved tmp : Fin T)
    (hreg : [width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,oldOverlap,nextOverlap,saved,tmp].Nodup)
    (V : ℕ) (old fresh kept tail queueTail : List (Fin (A+4)))
    (hB : fresh.length < 2^V) (hK : kept.length < 2^V)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = binSyms V fresh.length++binSyms V kept.length++queueTail)
    (hsrc : S.R src = fresh++kept++tail) (hold : S.R oldOverlap = old)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,nextOverlap,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ 2*old.length+18*fresh.length+28*kept.length+38*V+73 ∧
      Exec body (readEmitWindow width queue binary duplicate work bodyCount keepCount src archive oldOverlap nextOverlap saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update
          (Function.update (Function.update S.R queue queueTail) oldOverlap []) src tail)
          archive ((old++fresh++kept).reverse++S.R archive)) nextOverlap kept)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readCounts_exec (body := body) width nextOverlap queue binary bodyCount keepCount duplicate work saved tmp
    (by regs_nodup) V fresh.length kept.length hB hK queueTail v S hwidth
    (hblank _ (by simp)) hqueue (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  let M : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R
    queue queueTail) bodyCount (List.replicate fresh.length tick)) keepCount (List.replicate kept.length tick))}
  have off (i : Fin T) (hiq : i ≠ queue) (hib : i ≠ bodyCount) (hik : i ≠ keepCount) : M.R i = S.R i := by
    simp [M,hiq,hib,hik]
  obtain ⟨v₂,hu₂,he₂⟩ := emitWindow_exec (body := body) bodyCount keepCount src archive oldOverlap nextOverlap saved tmp
    (by regs_nodup) old fresh kept tail v₁ M
    (by simp [M,‹bodyCount ≠ keepCount›]) (by simp [M])
    (by rw [off src ‹queue ≠ src›.symm ‹bodyCount ≠ src›.symm ‹keepCount ≠ src›.symm]; exact hsrc)
    (by rw [off oldOverlap ‹queue ≠ oldOverlap›.symm ‹bodyCount ≠ oldOverlap›.symm ‹keepCount ≠ oldOverlap›.symm]; exact hold)
    (by rw [off nextOverlap ‹queue ≠ nextOverlap›.symm ‹bodyCount ≠ nextOverlap›.symm ‹keepCount ≠ nextOverlap›.symm]; exact hblank _ (by simp))
    (by rw [off saved ‹queue ≠ saved›.symm ‹bodyCount ≠ saved›.symm ‹keepCount ≠ saved›.symm]; exact hblank _ (by simp))
    (by rw [off tmp ‹queue ≠ tmp›.symm ‹bodyCount ≠ tmp›.symm ‹keepCount ≠ tmp›.symm]; exact hblank _ (by simp))
  let N : Stacks T A := {M with R := (Function.update (Function.update (Function.update (Function.update M.R
    oldOverlap []) src tail) archive ((old++fresh++kept).reverse++M.R archive)) nextOverlap kept)}
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [bodyCount,keepCount] (by regs_nodup) v₂ N
  have hb : (N.R bodyCount).length = fresh.length := by
    simp [N,M,‹bodyCount ≠ nextOverlap›,‹bodyCount ≠ archive›,‹bodyCount ≠ src›,‹bodyCount ≠ oldOverlap›,‹bodyCount ≠ keepCount›]
  have hk : (N.R keepCount).length = kept.length := by
    simp [N,M,‹keepCount ≠ nextOverlap›,‹keepCount ≠ archive›,‹keepCount ≠ src›,‹keepCount ≠ oldOverlap›]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,hb,hk] at he₃
  refine ⟨v₃,n₁+(2*old.length+4*fresh.length+14*kept.length+20)+(2*(fresh.length+(kept.length+0))+2*(1+(1+0))+1),
    hu₃.trans (hu₂.trans hu₁),by omega,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by omega) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hib : i = bodyCount
  · subst i
    simp [hblank,‹bodyCount ≠ nextOverlap›,‹bodyCount ≠ archive›,‹bodyCount ≠ src›,‹bodyCount ≠ oldOverlap›,‹queue ≠ bodyCount›.symm]
  by_cases hik : i = keepCount
  · subst i
    simp [hblank,‹keepCount ≠ nextOverlap›,‹keepCount ≠ archive›,‹keepCount ≠ src›,‹keepCount ≠ oldOverlap›,‹queue ≠ keepCount›.symm]
  by_cases hin : i = nextOverlap
  · subst i; simp [N,‹bodyCount ≠ nextOverlap›.symm,‹keepCount ≠ nextOverlap›.symm]
  by_cases hia : i = archive
  · subst i
    simp [N,M,‹archive ≠ nextOverlap›,‹bodyCount ≠ archive›.symm,‹keepCount ≠ archive›.symm,‹queue ≠ archive›.symm]
  by_cases his : i = src
  · subst i; simp [N,hib,hik,hin,hia]
  by_cases hio : i = oldOverlap
  · subst i; simp [N,hib,hik,hin,hia,his]
  · simp [N,M,hib,hik,hin,hia,his,hio]


end IntegerMultBounds.MathlibTM2.Routing.HaloWindowRun
