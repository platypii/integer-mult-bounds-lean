module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints

/-! Consume one binary dimension word into a reusable unary master. The
endpoint reader supplies conversion and scratch restoration; its duplicate
output is immediately retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readUnaryDimension (width zero queue binary dst duplicate work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (readSupplierEndpoints width zero queue binary dst duplicate work saved tmp) (uclear duplicate)

def readUnaryDimensionCost (V x : ℕ) : ℕ := 19*V+12*x+24

theorem readUnaryDimension_native (width zero queue binary dst duplicate work saved tmp : Fin T) :
    mnNativePushBound 3 (readUnaryDimension (P := P) (Q := Q) (A := A) (U := U)
      width zero queue binary dst duplicate work saved tmp) := by
  exact ⟨readSupplierEndpoints_native _ _ _ _ _ _ _ _ _,by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]⟩

theorem readUnaryDimension_exec (width zero queue binary dst duplicate work saved tmp : Fin T)
    (hreg : [width,zero,queue,binary,dst,duplicate,work,saved,tmp].Nodup)
    (V x : ℕ) (hfit : x < 2^V) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hqueue : S.R queue = binSyms V x++tail)
    (hblank : ∀ k ∈ [binary,dst,duplicate,work,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readUnaryDimensionCost V x ∧
      Exec body (readUnaryDimension width zero queue binary dst duplicate work saved tmp)
        (Host.mk v S) n (Host.mk v' {S with R :=
          (Function.update (Function.update S.R queue tail) dst (List.replicate x tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := readSupplierEndpoints_exec width zero queue binary dst duplicate
    work saved tmp hreg V x 0 hfit tail v S hwidth (by simp [hzero]) hqueue hblank
  simp only [Nat.add_zero] at he₁
  let M : Stacks T A := {S with R := (Function.update
    (Function.update (Function.update S.R queue tail) dst (List.replicate x tick)) duplicate (List.replicate x tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body duplicate v₁ M
  have he₂' : Exec body (uclear duplicate) (Host.mk v₁ M) (2*x+2)
      (Host.mk v₂ {S with R := Function.update (Function.update S.R queue tail) dst (List.replicate x tick)}) := by
    simp only [M,Function.update_self,List.length_replicate] at he₂
    refine he₂.cast rfl ?_
    apply congrArg (Host.mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = duplicate
    · subst k
      simp only [Function.update_self,Function.update_of_ne (Ne.symm ‹dst ≠ duplicate›),
        Function.update_of_ne (Ne.symm ‹queue ≠ duplicate›),hblank duplicate (by simp)]
    · simp only [Function.update_of_ne hk,M]
  refine ⟨v₂,n₁+(2*x+2),hu₂.trans hu₁,?_,Exec.seq he₁ he₂'⟩
  unfold readSupplierEndpointsCost at hn₁
  unfold readUnaryDimensionCost
  omega

theorem readUnaryDimension_exec_within (width zero queue binary dst duplicate work saved tmp : Fin T)
    (hreg : [width,zero,queue,binary,dst,duplicate,work,saved,tmp].Nodup)
    (V x : ℕ) (hfit : x < 2^V) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hzero : S.R zero = [])
    (hqueue : S.R queue = binSyms V x++tail)
    (hblank : ∀ k ∈ [binary,dst,duplicate,work,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readUnaryDimensionCost V x ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        3*readUnaryDimensionCost V x) depth
        (readUnaryDimension width zero queue binary dst duplicate work saved tmp)
        (Host.mk v S) n (Host.mk v' {S with R :=
          (Function.update (Function.update S.R queue tail) dst (List.replicate x tick))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := readUnaryDimension_exec width zero queue binary dst duplicate work saved tmp
    hreg V x hfit tail v S hwidth hzero hqueue hblank
  exact ⟨v',n,hu,hn,mn_native_exec_within he 3 (readUnaryDimension_native _ _ _ _ _ _ _ _ _) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
