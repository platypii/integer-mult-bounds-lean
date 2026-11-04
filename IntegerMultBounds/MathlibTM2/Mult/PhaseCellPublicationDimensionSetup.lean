module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddingCounterSetup
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Publication dimensions come from retained unary masters. The existing
straight-line setup language handles sums/products; padding supplies subtraction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

inductive PublicationDimensionReg
  | a | b | coreLength | wordWidth | rowCount | capacity | replicas
  | exponent | packet | padding | missing | saved | tmp | clock
  deriving DecidableEq

namespace PublicationDimensionReg
variable {T Q A : ℕ} {P U : Type}

def ops (e : PublicationDimensionReg → Fin T) : List (UnarySetup.Op T) :=
  [.add 1 (e .a) (e .exponent) (e .tmp),
   .add 1 (e .b) (e .exponent) (e .tmp),
   .mul (e .coreLength) (e .wordWidth) (e .packet) (e .saved) (e .tmp),
   .add 1 (e .replicas) (e .clock) (e .tmp)]

def program (e : PublicationDimensionReg → Fin T) : Pr P T Q A U :=
  .seq (UnarySetup.program (ops e))
    (paddingCounterSetup (e .rowCount) (e .capacity) (e .coreLength) (e .padding) (e .missing) (e .saved) (e .tmp))

def timeCost (a b L w N C B : ℕ) : ℕ :=
  ((4*a+4)+(4*b+4)+(L*(4*w+9)+4)+(4*B+4)+1)+paddingCounterSetupCost N C L

def loaded (e : PublicationDimensionReg → Fin T) (a b L w N C B : ℕ) (S : Stacks T A) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update S.R
    (e .exponent) (List.replicate (a+b) tick)) (e .packet) (List.replicate (L*w) tick))
      (e .clock) (List.replicate B tick)) (e .padding) (List.replicate ((C-N)*L) tick))}

theorem exec_within (body : P → Pr P T Q A U)
    (e : PublicationDimensionReg → Fin T) (he : Function.Injective e)
    (a b L w N C B : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (ha : (S.R (e .a)).length = a) (hb : (S.R (e .b)).length = b)
    (hcore : (S.R (e .coreLength)).length = L) (hword : (S.R (e .wordWidth)).length = w)
    (hrows : (S.R (e .rowCount)).length = N) (hcapacity : (S.R (e .capacity)).length = C)
    (hreplicas : (S.R (e .replicas)).length = B)
    (hfresh : ∀ r ∈ [exponent,packet,padding,missing,saved,tmp,clock], S.R (e r) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ timeCost a b L w N C B ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+2*timeCost a b L w N C B)
        depth (program e) (Host.mk v S) n (Host.mk v' (loaded e a b L w N C B S)) := by
  have hready : UnarySetup.Ready (ops e) S.R := by
    simp [ops,UnarySetup.Ready,UnarySetup.Op.Ready,UnarySetup.Op.runR,he.eq_iff,hfresh]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := UnarySetup.exec (body := body) (ops e) v S hready
  let M : Stacks T A := {S with R := UnarySetup.runR (ops e) S.R}
  have hframe (i : Fin T) (hi : ∀ r ∈ [exponent,packet,clock], i ≠ e r) : M.R i = S.R i := by
    apply UnarySetup.runR_off
    intro op hop
    simp only [ops,List.mem_cons,List.not_mem_nil,or_false] at hop
    rcases hop with rfl | rfl | rfl | rfl
    all_goals exact hi _ (by simp)
  have hread (r : PublicationDimensionReg) (hr : r ∉ [exponent,packet,clock]) : M.R (e r) = S.R (e r) := by
    apply hframe
    intro j hj h
    exact hr (he h ▸ hj)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := paddingCounterSetup_exec_within
    (e .rowCount) (e .capacity) (e .coreLength) (e .padding) (e .missing) (e .saved) (e .tmp)
    (by simp [he.eq_iff]) v₁ M
    (by rw [hread _ (by simp)]; exact hfresh _ (by simp))
    (by rw [hread _ (by simp)]; exact hfresh _ (by simp))
    (by rw [hread _ (by simp)]; exact hfresh _ (by simp))
    (by rw [hread _ (by simp)]; exact hfresh _ (by simp)) depth
  simp only [hread .rowCount (by simp),hread .capacity (by simp),hread .coreLength (by simp),
    hrows,hcapacity,hcore] at hn₂ he₂
  have hcost : UnarySetup.cost (ops e) S.R =
      (4*a+4)+(4*b+4)+(L*(4*w+9)+4)+(4*B+4)+1 := by
    simp [ops,UnarySetup.cost,UnarySetup.Op.cost,UnarySetup.Op.runR,he.eq_iff,
      ha,hb,hcore,hword,hreplicas]
    omega
  rw [hcost] at hn₁
  have hnative : mnNativePushBound 2 (UnarySetup.program (P := P) (Q := Q) (A := A) (U := U) (ops e)) := by
    simp [ops,UnarySetup.program,UnarySetup.Op.program,umul,umulSym,unaryProduct,ucopy,scanP,scanR,
      drainR,popDo,popPush,keepIn,pushN,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  have hw₁ := mn_native_exec_within he₁ 2 hnative depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn₁) (mnSize (Host.mk v S)+depth))
  have hwhole := mn_seq_within_add hw₁ he₂
  have hend : {M with R := Function.update M.R (e .padding) (List.replicate ((C-N)*L) tick)} =
      loaded e a b L w N C B S := by
    simp only [M,ops,UnarySetup.runR,UnarySetup.Op.runR]
    simp [loaded,he.eq_iff,hfresh,ha,hb,hcore,
      hword,hreplicas,List.replicate_append_replicate,Nat.add_comm]
  rw [hend] at hwhole
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  exact hwhole.mono (by intro d z hz; dsimp only [timeCost]; omega)


def outputs : List PublicationDimensionReg := [exponent,packet,clock,padding]

theorem retire_exec_within (body : P → Pr P T Q A U)
    (e : PublicationDimensionReg → Fin T) (he : Function.Injective e)
    (a b L w N C B : ℕ) (src dst : Fin T)
    (hoff : ∀ r ∈ outputs, e r ≠ src ∧ e r ≠ dst)
    (xs ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hfresh : ∀ r ∈ outputs, S.R (e r) = []) (depth : ℕ) :
    let M := loaded e a b L w N C B S
    let F : Stacks T A := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v F)+depth+0) depth
        (clearWords (outputs.map e)) (Host.mk v F)
        (2*((a+b)+L*w+B+(C-N)*L)+9)
        (Host.mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  dsimp only
  let M := loaded e a b L w N C B S
  let F : Stacks T A := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
  have hread (r : PublicationDimensionReg) (hr : r ∈ outputs) : F.R (e r) = M.R (e r) := by
    simp only [F,Function.update_of_ne (hoff r hr).1,Function.update_of_ne (hoff r hr).2]
  obtain ⟨v',hu,heclear⟩ := clearWords_exec (body := body) (outputs.map e)
    (by simp [outputs,he.eq_iff]) v F
  have hvol : ((outputs.map e).map (fun i => (F.R i).length)).sum = (a+b)+L*w+B+(C-N)*L := by
    simp only [outputs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [hread _ (by simp [outputs]),hread _ (by simp [outputs]),hread _ (by simp [outputs]),hread _ (by simp [outputs])]
    simp [M,loaded,he.eq_iff]
    omega
  rw [hvol] at heclear
  have htime : 2*((a+b)+L*w+B+(C-N)*L)+2*(outputs.map e).length+1 =
      2*((a+b)+L*w+B+(C-N)*L)+9 := by simp [outputs]
  rw [htime] at heclear
  have hend : {F with R := fun i => if i ∈ outputs.map e then [] else F.R i} =
      {S with R := (Function.update (Function.update S.R src xs) dst ys)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi : i ∈ outputs.map e
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hi
      simp only [ite_eq_left hi,Function.update_of_ne (hoff r hr).1,Function.update_of_ne (hoff r hr).2,hfresh r hr]
    · have hM : M.R i = S.R i := by
        simp only [outputs,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,
          not_or] at hi
        simp [M,loaded,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2]
      simp only [ite_eq_right hi,F,Function.update_apply]
      split_ifs <;> first | rfl | exact hM
  rw [hend] at heclear
  exact ⟨v',hu,mn_native_exec_within heclear 0 (clearWords_native _) depth _
    (by simp only [F,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end PublicationDimensionReg
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
