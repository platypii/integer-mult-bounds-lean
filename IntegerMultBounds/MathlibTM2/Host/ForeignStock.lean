module

public import IntegerMultBounds.MathlibTM2.Host.Foreign
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Transfer a preserved machine/stack invariant to a stock certificate for the
actual host simulation. Workspace is charged at transition boundaries, so the
allowance does not grow with the number of simulated transitions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

/-- A tape confined to a fixed interval retains that storage bound after a
transition whose new head also lies in the interval. Blank cells do not need
special cases in a caller's workspace invariant. -/
theorem stepStacks_interval (L R : List (Fin (A+4))) (w : Fin (A+4))
    (m : Move) (lo hi head : ℤ)
    (hhead : lo ≤ head ∧ head ≤ hi)
    (hnext : lo ≤ head+m.offset ∧ head+m.offset ≤ hi)
    (hL : (L.length : ℤ) ≤ head-lo) (hR : (R.length : ℤ) ≤ hi+1-head) :
    ((stepStacks blank L R w m).1.length : ℤ) ≤ head+m.offset-lo ∧
    ((stepStacks blank L R w m).2.length : ℤ) ≤ hi+1-(head+m.offset) := by
  cases m <;> cases L <;> cases R <;>
    simp only [stepStacks,Move.offset,List.length_cons,List.length_nil,List.tail_cons,List.tail_nil,
      Int.natCast_add,Int.natCast_one,Int.natCast_zero] at * <;> omega

private theorem peekScan_push (M : Program T Q A) :
    mnActPush (peekScan (U := U) M) = 0 := by
  unfold peekScan
  generalize List.finRange T = xs
  induction xs with
  | nil => rfl
  | cons i xs ih => simpa only [List.foldr_cons,mnActPush] using ih

theorem simIter_native (M : Program T Q A) :
    mnNativePushBound 2 (simIter (P := P) (U := U) M) := by
  have hlist : ∀ xs : List (Fin T), mnNativePushBound 2
      (Prog.seqList (P' := P) (xs.map (fun i => .act (tapeAct (Q := Q) (A := A) (U := U) i)) ++ [.act setState])) := by
    intro xs
    induction xs with
    | nil => simp [Prog.seqList,mnNativePushBound,setState,mnActPush]
    | cons i xs ih =>
      simpa [Prog.seqList,mnNativePushBound,tapeAct,mnActPush] using ih
  exact ⟨by simp only [mnNativePushBound,peekScan_push,Nat.zero_le],
    hlist _,by simp [mnNativePushBound,stopFlag,mnActPush]⟩

/-- A boundary invariant supplies the stock bound. Only the fixed cost of one
simulated transition is added, rather than the cost of the complete run. -/
theorem sim_loop_within (M : Program T Q A) (body : P → Pr P T Q A U)
    (I : Config T Q A → Stacks T A → Prop) (B depth : ℕ)
    (hbound : ∀ c S, I c S → ∀ v : HS T Q A U, mnSize (mk v S) ≤ B)
    (hpreserve : ∀ c S st' act, I c S →
      M.transition c.state (fun i => c.tape i (c.head i)) = some (st',act) →
      ∀ c', step M c = some c' →
        I c' {S with L := newL S act, R := newR S act}) :
    ∀ k c v S, I c S → Rep c S.L S.R → v.st = c.state → v.flag = true →
    ∀ cf, run M k c = some cf → step M cf = none →
    ∃ v' S',
      ExecWithin body (fun d z => mnSize z+d ≤ B+depth+2*(T+4)) depth
        (.loop (·.flag) (simIter M)) (mk v S) (k*(T+5)+5) (mk v' S') ∧
      Rep cf S'.L S'.R ∧ v'.user = v.user ∧ I cf S' ∧
      S'.inp = S.inp ∧ S'.out = S.out := by
  intro k
  induction k with
  | zero =>
    intro c v S hI hrep hst hflag cf hrun hhalt
    simp only [run,Option.some.injEq] at hrun
    subst cf
    have ht : M.transition c.state (fun i => c.tape i (c.head i)) = none := by
      unfold step at hhalt
      split at hhalt
      · assumption
      · simp at hhalt
    obtain ⟨v',hu,hflag',hst',he⟩ := simIter_halt body M hrep hst ht
    have hb := hbound c S hI v
    have hw := mn_native_exec_within he 2 (simIter_native M) depth (B+depth+2*(T+4)) (by omega)
    have hf := hbound c S hI v'
    refine ⟨v',S,?_,hrep,hu,hI,rfl,rfl⟩
    simpa using ExecWithin.loop_true hflag hw (ExecWithin.loop_false (by simpa using hflag') (by omega))
  | succ k ih =>
    intro c v S hI hrep hst hflag cf hrun hhalt
    simp only [run] at hrun
    cases hs : step M c with
    | none => simp [hs] at hrun
    | some c₁ =>
      rw [hs,Option.bind_some] at hrun
      obtain ⟨st',act,ht⟩ : ∃ st' act,
          M.transition c.state (fun i => c.tape i (c.head i)) = some (st',act) := by
        unfold step at hs
        split at hs
        · simp at hs
        · exact ⟨_,_,by assumption⟩
      obtain ⟨c',hc',hcs,hrep'⟩ := rep_step hrep ht
      rw [hs,Option.some.injEq] at hc'
      subst c'
      obtain ⟨v₁,hu,hflag',hst',he⟩ := simIter_step body M hrep hst ht
      have hI' := hpreserve c S st' act hI ht c₁ hs
      obtain ⟨v',S',hw,hrep'',hu',hI'',hi,ho⟩ := ih c₁ v₁
        {S with L := newL S act,R := newR S act} hI' hrep'
        (by rw [hst',hcs]) (by rw [hflag',hflag]) cf hrun hhalt
      have hb := hbound c S hI v
      have hw₁ := mn_native_exec_within he 2 (simIter_native M) depth (B+depth+2*(T+4)) (by omega)
      refine ⟨v',S',?_,hrep'',hu'.trans hu,hI'',hi,ho⟩
      convert ExecWithin.loop_true hflag hw₁ hw using 1; ring

/-- A machine contract and a preserved stock invariant certify the complete
foreign call, including initialization and the final halt test. -/
theorem foreign_exec_within (M : Program T Q A) (body : P → Pr P T Q A U)
    {pre post : TapePred T A} {k : ℕ} (h : HoareTime M pre post k)
    (I : Config T Q A → Stacks T A → Prop) (B depth : ℕ)
    (hbound : ∀ c S, I c S → ∀ v : HS T Q A U, mnSize (mk v S) ≤ B)
    (hpreserve : ∀ c S st' act, I c S →
      M.transition c.state (fun i => c.tape i (c.head i)) = some (st',act) →
      ∀ c', step M c = some c' →
        I c' {S with L := newL S act, R := newR S act})
    (v : HS T Q A U) (S : Stacks T A) (w : Tapes T A) (hw : pre w)
    (hrep : RepT w S.L S.R) (hI : I (w.start M) S) :
    ∃ v' S' w', post w' ∧ RepT w' S'.L S'.R ∧ v'.user = v.user ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧
      ∃ m ≤ k*(T+5)+6,
        ExecWithin body (fun d z => mnSize z+d ≤ B+depth+2*(T+4)) depth
          (foreign M) (mk v S) m (mk v' S') := by
  obtain ⟨kk,c,hkk,hrun,hhalt,hpost⟩ := h w hw
  obtain ⟨v',S',he,hrep',hu,hI',hi,ho⟩ := sim_loop_within M body I B depth hbound hpreserve
    kk (w.start M) {v with flag := true,st := M.start} S hI hrep rfl rfl c hrun hhalt
  have hb := hbound (w.start M) S hI v
  have hb' := hbound (w.start M) S hI {v with flag := true,st := M.start}
  refine ⟨v',S',c.tapes,hpost,hrep',hu,hi,ho,1+(kk*(T+5)+5),?_,?_⟩
  · have := Nat.mul_le_mul_right (T+5) hkk
    omega
  · have hinit : ExecWithin body (fun d z => mnSize z+d ≤ B+depth+2*(T+4)) depth
        (.act (.load (fun v => {v with flag := true,st := M.start}) .done))
        (mk v S) 1 (mk {v with flag := true,st := M.start} S) :=
      ExecWithin.act _ _ (by omega) (by exact Nat.add_le_add_right hb' depth |>.trans (by omega))
    exact ExecWithin.seq hinit he

end IntegerMultBounds.MathlibTM2.Host
