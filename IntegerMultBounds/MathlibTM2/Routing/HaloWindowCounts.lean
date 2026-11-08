module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadUnaryDimension

/-! Load the two varying counts of a monotone window from ordinary binary
metadata. The empty next-overlap bank supplies the decoder's zero input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloWindowCounts
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readCounts (width zero queue binary bodyCount keepCount duplicate work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (readUnaryDimension width zero queue binary bodyCount duplicate work saved tmp)
    (readUnaryDimension width zero queue binary keepCount duplicate work saved tmp)

theorem readCounts_native (width zero queue binary bodyCount keepCount duplicate work saved tmp : Fin T) :
    mnNativePushBound 3 (readCounts (P := P) (Q := Q) (A := A) (U := U)
      width zero queue binary bodyCount keepCount duplicate work saved tmp) :=
  ⟨readUnaryDimension_native _ _ _ _ _ _ _ _ _,readUnaryDimension_native _ _ _ _ _ _ _ _ _⟩

theorem readCounts_exec (width zero queue binary bodyCount keepCount duplicate work saved tmp : Fin T)
    (hreg : [width,zero,queue,binary,bodyCount,keepCount,duplicate,work,saved,tmp].Nodup)
    (V B K : ℕ) (hB : B < 2^V) (hK : K < 2^V) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hqueue : S.R queue = binSyms V B++binSyms V K++tail)
    (hblank : ∀ i ∈ [binary,bodyCount,keepCount,duplicate,work,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ 38*V+12*B+12*K+48 ∧
      Exec body (readCounts width zero queue binary bodyCount keepCount duplicate work saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update S.R
          queue tail) bodyCount (List.replicate B tick)) keepCount (List.replicate K tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readUnaryDimension_exec (body := body) width zero queue binary bodyCount duplicate work saved tmp
    (by regs_nodup) V B hB (binSyms V K++tail) v S hwidth hzero
    (by simpa only [List.append_assoc] using hqueue)
    (by intro i hi; exact hblank i (by simp only [List.mem_cons] at hi ⊢; tauto))
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R queue (binSyms V K++tail))
    bodyCount (List.replicate B tick))}
  have off (i : Fin T) (hiq : i ≠ queue) (hib : i ≠ bodyCount) : M.R i = S.R i := by simp [M,hiq,hib]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := readUnaryDimension_exec (body := body) width zero queue binary keepCount duplicate work saved tmp
    (by regs_nodup) V K hK tail v₁ M
    (by rw [off width ‹width ≠ queue› ‹width ≠ bodyCount›]; exact hwidth)
    (by rw [off zero ‹zero ≠ queue› ‹zero ≠ bodyCount›]; exact hzero)
    (by simp [M,‹queue ≠ bodyCount›]) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [off _ (by first | assumption | exact Ne.symm (by assumption))
          (by first | assumption | exact Ne.symm (by assumption))] <;>
        exact hblank _ (by simp))
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · unfold readUnaryDimensionCost at hn₁ hn₂
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i = keepCount
    · subst i; simp
    by_cases hb : i = bodyCount
    · subst i; simp [M,‹bodyCount ≠ keepCount›,‹queue ≠ bodyCount›.symm]
    by_cases hq : i = queue
    · subst i; simp [M,‹queue ≠ keepCount›,‹queue ≠ bodyCount›]
    · simp [M,hi,hb,hq]

end IntegerMultBounds.MathlibTM2.Routing.HaloWindowCounts
