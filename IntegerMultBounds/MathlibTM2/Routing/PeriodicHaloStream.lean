module

public import IntegerMultBounds.MathlibTM2.Routing.RegularHaloStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadPrefixInPlace

/-! Periodic extension and actual persistent-halo emission of one current fiber.
Extension scans only that fiber. Its archive/decoder scratch is reused by the
monotone scan, so no second bank of payload tapes is allocated. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.PeriodicHaloStream
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz HaloIntervalLayout RegularHaloLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def extended (A w H : ℕ) (xs : List GaussianInt) : List (Fin (A+4)) :=
  cstream A w (xs.drop (xs.length-H)++xs++xs.take H)

def emit (full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) : Pr P T Q A U :=
  .seq (padPrefixInPlace full band skip src archive binary saved tmp work)
    (HaloStream.emit clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)

theorem emit_native
    (full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) :
    mnNativePushBound 3 (emit (P := P) (Q := Q) (A := A) (U := U)
      full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp) := by
  refine ⟨?_,HaloStream.emit_native _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  simp [padPrefixInPlace,copySlice,copyPrefix,discardPrefix,transfer,scanR,keepIn,transferAct,
    copyR,copyStep,moveR,moveStep,whileR,peekR,uclear,drainR,popDo,mnNativePushBound,mnActPush]

theorem emit_periodic_exec
    (full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [full,band,skip,clock,width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (w V L H N : ℕ) (xs : List GaussianInt) (hN : 0 < N) (hgap : 2*H ≤ L)
    (hlen : xs.length = N*L) (hfit : (N*L+2*H)*w < 2^V)
    (tail queueTail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hfull : (S.R full).length = xs.length*w) (hband : (S.R band).length = H*w)
    (hskip : (S.R skip).length = (xs.length-H)*w)
    (hclock : (S.R clock).length = (pairs (L*w) (H*w) 0 N).length) (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = metadata V 0 (pairs (L*w) (H*w) 0 N)++queueTail)
    (hsrc : S.R src = cstream A w xs++tail)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,archive,overlap,spare,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ (26*xs.length+28*H)*w+34*((N*L+2*H)*w)+N*(76*V+149)+50 ∧
      Exec body (emit full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf {S with R := (Function.update (Function.update (Function.update S.R clock [])
          queue queueTail) src ((List.range' 0 N).flatMap (fun j =>
            slice (extended A w H xs) (j*(L*w)) ((j+1)*(L*w)+2*(H*w)))++tail))}) := by
  have hr := hreg
  regs_ne hr
  have hH : H ≤ xs.length := by
    have hh : L ≤ N*L := Nat.le_mul_of_pos_left L hN
    omega
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := padPrefixInPlace_exec (body := body)
    (full := full) (band := band) (skip := skip) (src := src) (dst := archive)
    (savedSkip := binary) (saved := saved) (tmp := tmp) (buf := work)
    (by regs_nodup) w H xs hH tail v S hfull hband hskip hsrc (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by simp))
  let M : Stacks T A := {S with R := Function.update S.R src (extended A w H xs++tail)}
  have hrow : (extended A w H xs).length = N*(L*w)+2*(H*w) := by
    simp only [extended,length_cstream,List.length_append,List.length_drop,List.length_take,Nat.min_eq_left hH]
    have he : xs.length-(xs.length-H)+xs.length+H = xs.length+2*H := by omega
    rw [he,hlen]
    ring
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := RegularHaloStream.emit_regular_exec (body := body)
    clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp
    (by regs_nodup) (extended A w H xs) V (L*w) (H*w) N hN
    (by nlinarith only [Nat.mul_le_mul_right w hgap]) hrow
    (by rw [hrow]; convert hfit using 1; ring) tail queueTail v₁ M
    (by simpa [M,‹clock ≠ src›] using hclock) (by simpa [M,‹width ≠ src›] using hwidth)
    (by simpa [M,‹queue ≠ src›] using hqueue) (by simp [M]) (by
      intro i hi
      have hbi := hblank i hi
      have his : i ≠ src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | assumption | exact Ne.symm (by assumption)
      simpa [M,his] using hbi)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · have he : N*(L*w)+2*(H*w) = (N*L+2*H)*w := by ring
    rw [he] at hn₂
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hic : i = clock
    · subst i; simp [‹clock ≠ src›,‹clock ≠ queue›]
    by_cases hiq : i = queue
    · subst i; simp [‹queue ≠ src›]
    by_cases his : i = src
    · subst i; simp
    · simp [M,hic,hiq,his]

theorem emit_within_stock
    {full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T}
    {v vf : HS T Q A U} {S F : Stacks T A} {n C : ℕ}
    (hex : Exec body (emit full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (mk v S) n (mk vf F)) (hn : n ≤ C) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*C) depth
      (emit full band skip clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
      (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 3 (emit_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.PeriodicHaloStream
