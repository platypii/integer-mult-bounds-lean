module

public import IntegerMultBounds.MathlibTM2.Routing.HaloScan

/-! Complete monotone halo emission in ordinary order, including archive
retirement. Its input descriptor list is structural proof data, not unrolled code. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloStream
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  HaloScanLayout HaloScan
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def emit (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) : Pr P T Q A U :=
  .seq (scan clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
    (moveR archive src id)

theorem emit_native (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) :
    mnNativePushBound 3 (emit (P := P) (Q := Q) (A := A) (U := U)
      clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp) := by
  refine ⟨scan_native _ _ _ _ _ _ _ _ _ _ _ _ _ _,?_⟩
  simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem emit_exec
    (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [clock,width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (V : ℕ) (xs : List (WindowPair (Fin (A+4))))
    (hfit : ∀ x ∈ xs, x.Fits V) (hfinal : remainingOverlap [] xs = []) (tail queueTail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = xs.length) (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = xs.flatMap (WindowPair.metadata V)++queueTail)
    (hsrc : S.R src = xs.flatMap WindowPair.input++tail)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,archive,overlap,spare,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ 34*(xs.flatMap WindowPair.input).length+xs.length*(76*V+149)+4 ∧
      Exec body (emit clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update S.R clock [])
          queue queueTail) src (output [] xs++tail))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := scan_exec (body := body)
    clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp hreg V [] xs
    hfit tail queueTail v S hclock hwidth hqueue hsrc (hblank _ (by simp)) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  let F := finish clock queue src archive overlap S [] xs tail queueTail
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body archive src ‹src ≠ archive›.symm id v₁ F
  have ha : F.R archive = (output [] xs).reverse := by
    simp [F,finish,‹archive ≠ overlap›,hblank]
  have hs : F.R src = tail := by simp [F,finish,‹src ≠ overlap›,‹src ≠ archive›]
  refine ⟨v₂,n₁+(2*(F.R archive).length+2),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · have hl := output_length_le ([] : List (Fin (A+4))) xs
    rw [ha,List.length_reverse]
    simp only [List.length_nil,Nat.mul_zero,Nat.zero_add] at hn₁ hl
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [movedR,ha,hs]
    by_cases hia : i = archive
    · subst i
      simp [movedR,hblank,‹src ≠ archive›.symm,‹clock ≠ archive›.symm,‹queue ≠ archive›.symm]
    by_cases hio : i = overlap
    · subst i
      simp [movedR,F,finish,hfinal,hblank,‹src ≠ overlap›.symm,‹archive ≠ overlap›.symm,
        ‹clock ≠ overlap›.symm,‹queue ≠ overlap›.symm]
    · simp [movedR,F,finish,his,hia,hio]

theorem emit_within_stock
    {clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T}
    {v vf : HS T Q A U} {S F : Stacks T A} {n V N W : ℕ}
    (hex : Exec body (emit clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (mk v S) n (mk vf F)) (hn : n ≤ 34*W+N*(76*V+149)+4) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(34*W+N*(76*V+149)+4)) depth
      (emit clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 3 (emit_native _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.HaloStream
