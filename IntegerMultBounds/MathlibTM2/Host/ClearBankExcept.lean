module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Retire a generated finite bank while preserving one borrowed seed. The
proof is structural and needs no enumeration of the concrete register layout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def bankExcept (work : Fin N → Fin T) (keep : Fin N) : List (Fin T) :=
  (List.ofFn work).filter (fun k => decide (k ≠ work keep))

def clearBankExcept (work : Fin N → Fin T) (keep : Fin N) : Pr P T Q A U :=
  clearWords (bankExcept work keep)

private theorem clearWords_native_zero (rs : List (Fin T)) :
    mnNativePushBound 0 (clearWords (P := P) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush],ih⟩

private theorem sum_filter_le {β : Type} (xs : List β) (p : β → Bool) (f : β → ℕ) :
    ((xs.filter p).map f).sum ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons,List.map_cons,List.sum_cons]
    split
    · simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add_left ih (f x)
    · exact ih.trans (Nat.le_add_left _ _)

theorem clearBankExcept_exec (work : Fin N → Fin T) (hwork : Function.Injective work) (keep : Fin N)
    (base : Regs T A) (v : HS T Q A U) (S : Stacks T A)
    (hkeep : S.R (work keep) = base (work keep))
    (hblank : ∀ i, i ≠ keep → base (work i) = [])
    (hframe : ∀ k, (∀ i, k ≠ work i) → S.R k = base k) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2*(∑ i, (S.R (work i)).length)+2*N+1 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth) depth
        (clearBankExcept work keep) (Host.mk v S) n (Host.mk v' {S with R := base}) := by
  classical
  have hnd : (bankExcept work keep).Nodup :=
    (List.nodup_ofFn.mpr hwork).filter _
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) (bankExcept work keep) hnd v S
  have hfinal : (fun k => if k ∈ bankExcept work keep then [] else S.R k) = base := by
    funext k
    by_cases hw : ∃ i, work i = k
    · obtain ⟨i,rfl⟩ := hw
      by_cases hi : i = keep
      · subst i
        simpa only [bankExcept,List.mem_filter,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,and_false,
          if_false] using hkeep
      · have hm : work i ∈ bankExcept work keep := by
          simp only [bankExcept,List.mem_filter,decide_eq_true_eq]
          exact ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,hwork.ne hi⟩
        rw [if_pos hm,hblank i hi]
    · have hn : k ∉ bankExcept work keep := by
        intro hk
        have hm := List.mem_of_mem_filter hk
        obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
        exact hw ⟨i,hi⟩
      rw [if_neg hn]
      exact hframe k (by intro i hi; exact hw ⟨i,hi.symm⟩)
  rw [hfinal] at he
  have hsum := sum_filter_le (List.ofFn work) (fun k => decide (k ≠ work keep)) (fun k => (S.R k).length)
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn] at hsum
  have hlen : (bankExcept work keep).length ≤ N :=
    (List.length_filter_le ..).trans_eq List.length_ofFn
  have htime : 2*((bankExcept work keep).map (fun k => (S.R k).length)).sum+
      2*(bankExcept work keep).length+1 ≤ 2*(∑ i, (S.R (work i)).length)+2*N+1 := by
    change ((bankExcept work keep).map (fun k => (S.R k).length)).sum ≤ _ at hsum
    omega
  refine ⟨v',_,hu,htime,?_⟩
  apply mn_native_exec_within he 0 (clearWords_native_zero _) depth _
  omega

end IntegerMultBounds.MathlibTM2.Host
