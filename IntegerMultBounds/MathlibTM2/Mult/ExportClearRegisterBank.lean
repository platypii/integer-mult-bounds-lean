module

public import IntegerMultBounds.MathlibTM2.Mult.ClearRegisterBankStock
public import IntegerMultBounds.MathlibTM2.Host.OrderedMoveStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Export a published word in order, then release both sides of the entire
private bank. The structural execution allocates no additional tape stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def clearedRegisterBank (bank : Fin N → Fin T) (S : Stacks T A) : Stacks T A :=
  {S with L := fun k => if k ∈ List.ofFn bank then [] else S.L k
          R := fun k => if k ∈ List.ofFn bank then [] else S.R k}

def clearRegisterBankCost (bank : Fin N → Fin T) (S : Stacks T A) : ℕ :=
  ((List.ofFn bank).map (fun r => 4*(S.L r).length+2*(S.R r).length)).sum+4*N+1

def exportClearRegisterBank (bank : Fin N → Fin T) (src tmp : Fin N) (dst : Fin T) : Pr P T Q A U :=
  .seq (moveRightOrdered (bank src) (bank tmp) dst) (clearRegisters (List.ofFn bank))

def exportClearRegisterBankCost (bank : Fin N → Fin T) (src : Fin N) (dst : Fin T) (S : Stacks T A) : ℕ :=
  (4*(S.R (bank src)).length+4)+clearRegisterBankCost bank
    {S with R := (Function.update (Function.update S.R (bank src) []) dst (S.R (bank src)++S.R dst))}

theorem clearRegisterBankCost_le (bank : Fin N → Fin T) (S : Stacks T A) :
    clearRegisterBankCost bank S ≤ 4*registerBankStock (embStk bank S)+4*N+1 := by
  unfold clearRegisterBankCost registerBankStock
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,embStk_L,embStk_R]
  have hh : (∑ i : Fin N, (4*(S.L (bank i)).length+2*(S.R (bank i)).length)) ≤
      ∑ i : Fin N, 4*((S.L (bank i)).length+(S.R (bank i)).length) := by
    apply Finset.sum_le_sum
    intro i _
    omega
  rw [←Finset.mul_sum] at hh
  omega

/-- Export and full cleanup cost only linear private stock, regardless of how
many symbols remain in arithmetic scratch. -/
theorem exportClearRegisterBankCost_le (bank : Fin N → Fin T) (src : Fin N) (dst : Fin T)
    (hdst : ∀ i, bank i ≠ dst) (S : Stacks T A) :
    exportClearRegisterBankCost bank src dst S ≤ 8*registerBankStock (embStk bank S)+4*N+5 := by
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (bank src) []) dst (S.R (bank src)++S.R dst))}
  have hstock : registerBankStock (embStk bank M) ≤ registerBankStock (embStk bank S) := by
    unfold registerBankStock
    apply Finset.sum_le_sum
    intro i _
    change (S.L (bank i)).length+(M.R (bank i)).length ≤
      (S.L (bank i)).length+(S.R (bank i)).length
    by_cases hi : bank i = bank src
    · simp [M,hi,hdst src]
    · simp [M,hi,hdst i]
  have hsrc : (S.R (bank src)).length ≤ registerBankStock (embStk bank S) := by
    have hh := Finset.single_le_sum
      (f := fun i : Fin N => (S.L (bank i)).length+(S.R (bank i)).length)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ src)
    change (S.R (bank src)).length ≤ ∑ i : Fin N, ((S.L (bank i)).length+(S.R (bank i)).length)
    omega
  have hh := clearRegisterBankCost_le bank M
  change (4*(S.R (bank src)).length+4)+clearRegisterBankCost bank M ≤ _
  omega

theorem exportClearRegisterBank_exec (bank : Fin N → Fin T) (hbank : Function.Injective bank)
    (src tmp : Fin N) (hst : src ≠ tmp) (dst : Fin T) (hdst : ∀ i, bank i ≠ dst)
    (v : HS T Q A U) (S : Stacks T A) (htmp : S.R (bank tmp) = []) (depth B : ℕ)
    (hB : mnSize (mk v S)+depth ≤ B) :
    let M := {S with R := (Function.update (Function.update S.R (bank src) []) dst (S.R (bank src)++S.R dst))}
    let F := clearedRegisterBank bank {S with R := Function.update S.R dst (S.R (bank src)++S.R dst)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ B) depth (exportClearRegisterBank bank src tmp dst)
        (mk v S) ((4*(S.R (bank src)).length+4)+clearRegisterBankCost bank M) (mk v' F) ∧
      (∀ i, F.L (bank i) = [] ∧ F.R (bank i) = []) ∧
      F.R dst = S.R (bank src)++S.R dst ∧
      (∀ k, k ≠ dst → (∀ i, bank i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) := by
  dsimp only
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R (bank src) []) dst (S.R (bank src)++S.R dst))}
  let E : Stacks T A := {S with R := Function.update S.R dst (S.R (bank src)++S.R dst)}
  obtain ⟨v₁,hu₁,he₁⟩ := moveRightOrdered_exec (body := body) (bank src) (bank tmp) dst
    (hbank.ne hst) (hdst src) (hdst tmp) v S htmp
  have hw₁ := moveRightOrdered_within (bank src) (bank tmp) dst he₁ depth B hB
  obtain ⟨v₂,hu₂,he₂⟩ := clearRegisters_exec (body := body) (List.ofFn bank)
    (List.nodup_ofFn_ofInjective hbank) v₁ M
  have hw₂ := clearRegisters_within (List.ofFn bank) he₂ depth B hw₁.final
  have hfinal : clearedRegisterBank bank M = clearedRegisterBank bank E := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k ∈ List.ofFn bank
    · simp only [clearedRegisterBank,ite_eq_left hk]
    · have hne : k ≠ bank src := by
        intro he
        subst k
        exact hk (List.mem_ofFn.mpr ⟨src,rfl⟩)
      by_cases hd : k = dst
      · subst k; simp only [clearedRegisterBank,ite_eq_right hk,M,E,Function.update_self]
      · simp only [clearedRegisterBank,ite_eq_right hk,M,E,Function.update_of_ne hd,Function.update_of_ne hne]
  change ExecWithin body _ _ _ _ _ (mk v₂ (clearedRegisterBank bank M)) at hw₂
  rw [hfinal] at hw₂
  refine ⟨v₂,hu₂.trans hu₁,?_,?_,?_,?_⟩
  · have hw := ExecWithin.seq hw₁ hw₂
    simpa only [exportClearRegisterBank,clearRegisterBankCost,List.length_ofFn] using hw
  · intro i
    have hm : bank i ∈ List.ofFn bank := List.mem_ofFn.mpr ⟨i,rfl⟩
    simp only [clearedRegisterBank,ite_eq_left hm,and_self]
  · have hn : dst ∉ List.ofFn bank := by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      exact hdst i hi
    simp only [clearedRegisterBank,ite_eq_right hn,Function.update_self]
  · intro k hk hoff
    have hn : k ∉ List.ofFn bank := by
      intro hm
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
      exact hoff i hi
    simp only [clearedRegisterBank,ite_eq_right hn,Function.update_of_ne hk,and_self]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
