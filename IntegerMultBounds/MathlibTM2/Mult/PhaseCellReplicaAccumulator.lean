module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocateZeroLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorPlacement
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Initialize the independent packed replica output from retained row count and
symbol volume. The original RHS and all numerical/gather headers survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def initializeReplicaAccumulator (plan : ReplicaInteriorPlacement T) (dst : Fin T) : Pr P T Q A U :=
  allocateZeroLine (plan.gather 121) (plan.gather 123) dst
    (plan.gather 88) (plan.gather 89) (plan.gather 104)

def replicaZeroRows (A N span w : ℕ) : List (List (Fin (A+4))) :=
  List.replicate N (cstream A w (List.replicate span 0))

theorem replicaZeroRows_length (A N span w : ℕ) : (replicaZeroRows A N span w).length = N := by
  simp [replicaZeroRows]

theorem replicaZeroRows_row_length (A N span w : ℕ) :
    ∀ row ∈ replicaZeroRows A N span w, row.length = span*w := by
  intro row hrow
  obtain rfl := (List.mem_replicate.mp hrow).2
  simp [length_cstream]

theorem replicaZeroRows_range (A N span w q e : ℕ) :
    ∀ row ∈ replicaZeroRows A N span w, EncodedRange A w q e row := by
  intro row hrow
  obtain rfl := (List.mem_replicate.mp hrow).2
  exact encodedRange_zero_words A span w q e

theorem replicaZeroRows_flatten (A N span w : ℕ) :
    (replicaZeroRows A N span w).flatten = cstream A (span*w) (List.replicate N 0) := by
  simp only [replicaZeroRows,cstream_replicate_zero]
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [List.replicate_succ,List.flatten_cons,ih,← List.replicate_add]
    congr 1
    simp [Nat.add_mul,Nat.add_comm]

theorem initializeReplicaAccumulator_exec_within (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ k, plan.gather k ≠ dst) (N span w : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R (plan.gather 121)).length = N)
    (hvolume : (S.R (plan.gather 123)).length = span*w)
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,104], S.R (plan.gather k) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ allocateZeroLineCost N (span*w) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*allocateZeroLineCost N (span*w)) depth
        (initializeReplicaAccumulator plan dst) (mk v S) n
        (mk v' {S with R := Function.update S.R dst ((replicaZeroRows A N span w).flatten++S.R dst)}) := by
  have hregs : [plan.gather 121,plan.gather 123,dst,plan.gather 88,plan.gather 89,plan.gather 104].Nodup := by
    simp [List.nodup_cons,hgd,Ne.symm (hgd _),plan.gather_injective.eq_iff]
  obtain ⟨v',n,hu,hn,he⟩ := allocateZeroLine_exec (body := body)
    (plan.gather 121) (plan.gather 123) dst (plan.gather 88) (plan.gather 89) (plan.gather 104)
    hregs N (span*w) v S hN hvolume
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp))
  rw [← replicaZeroRows_flatten A N span w] at he
  refine ⟨v',n,hu,hn,mn_native_exec_within he 2 ?_ depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hn) _)⟩
  simp [allocateZeroLine,unaryProduct,umulSym,ucopy,scanP,scanR,keepIn,pushN,
    uclear,drainR,popDo,moveR,moveStep,whileR,popPush,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
