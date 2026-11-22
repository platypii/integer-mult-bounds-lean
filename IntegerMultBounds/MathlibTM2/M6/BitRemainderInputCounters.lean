module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHandoffPlacement

/-! Build the forward transpose clocks using only its eight tapes and two retained widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
open IntegerMultBounds.Machine Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem inputCounters_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin 8 ↪ Fin T) (blocks width : Fin T) (distinct : blocks ≠ width)
    (apart : ∀ i, blocks ≠ bank i ∧ width ≠ bank i) :
    ∃ code, ∀ B K u S, S.R blocks = binSyms B.size B → S.R width = binSyms K.size K →
      (∀ i, S.R (bank i) = []) →
      ∃ v F t, Exec body code (mk u S) t (mk v F) ∧
        t ≤ B.size*(12*(B.size+K.size)+20)+30*(B.size+K.size)+11*K.size+8*(K+B*K)+50 ∧
        v.user = u.user ∧ F.L = S.L ∧
        (∀ i, F.R (bank i) = (transposeStacks (embStk bank S) [] [] []
          (List.replicate K Node.tick) (List.replicate (B*K) Node.tick)).R i) ∧
        ∀ j, j ≠ bank 4 → j ≠ bank 7 → F.R j = S.R j := by
  let product : Pr P T Q prime U := bmul blocks width (bank 3) (bank 0) (bank 1) (bank 2) (bank 5) (bank 6) blocks
  let emit (src : Fin T) (i : Fin 8) : Pr P T Q prime U :=
    emitRun src (bank 0) (bank i) (bank 1) (bank 2) (bank 5) Node.tick
  refine ⟨product.seq ((emit width 4).seq ((emit (bank 3) 7).seq (bclear (bank 3)))),?_⟩
  intro B K u S b k empty
  have regs : [blocks,width,bank 3,bank 0,bank 1,bank 2,bank 5,bank 6].Nodup := by
    simp [distinct,apart,bank.injective.eq_iff]
  obtain ⟨v,m,user,bill,mul⟩ := bmul_exec (body := body) regs (apart 3).1 (apart 0).1
    (Nat.lt_size_self B) (Nat.lt_size_self K) u S b k (empty 3) (empty 0) (empty 1) (empty 2) (empty 5) (empty 6)
  let D := {S with R := Function.update S.R (bank 3) (binSyms (B.size+K.size) (B*K))}
  have free (i : Fin 8) (hi : i ≠ 3) : D.R (bank i) = [] := by simp [D,Function.update_of_ne (bank.injective.ne hi),empty]
  have fresh (r) (h : r ∈ [bank 0,bank 1,bank 2,bank 5]) : D.R r = [] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl <;> exact free _ (by decide)
  have ports : [width,bank 0,bank 4,bank 1,bank 2,bank 5].Nodup := by simp [apart,bank.injective.eq_iff]
  obtain ⟨y,n,same,fee,record⟩ := emitRun_exec (body := body) ports _ _ (Nat.lt_size_self K)
    Node.tick v D (by simp [D,Function.update_of_ne (apart 3).2,k]) fresh
  rw [free 4 (by decide),List.append_nil] at record
  let E := {D with R := Function.update D.R (bank 4) (List.replicate K Node.tick)}
  have ports' := (by decide : ([3,0,7,1,2,5] : List (Fin 8)).Nodup).map bank.injective
  have bound : B*K < 2^(B.size+K.size) := by
    rw [pow_add]; exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self B) (Nat.lt_size_self K).le (by positivity)
  obtain ⟨z,r,keep,charge,row⟩ := emitRun_exec (body := body) ports' _ _ bound Node.tick y E
    (by simp [E,D,Function.update_apply,bank.injective.eq_iff])
    (fun j h => by
      have neq : j ≠ bank 4 := by rintro rfl; simpa [bank.injective.eq_iff] using h
      exact (Function.update_of_ne neq _ _).trans (fresh j h))
  rw [show E.R (bank 7) = [] by simp [E,Function.update_apply,bank.injective.eq_iff,free],List.append_nil] at row
  let G := {E with R := Function.update E.R (bank 7) (List.replicate (B*K) Node.tick)}
  obtain ⟨v',saved,_,clear⟩ := bclear_exec body (bank 3) z G
  have len : (G.R (bank 3)).length = B.size+K.size := by simp [G,E,D,Function.update_apply,bank.injective.eq_iff,length_binSyms]
  rw [len] at clear
  refine ⟨v',_,_,Exec.seq mul (Exec.seq record (Exec.seq row clear)),by omega,saved.trans (keep.trans (same.trans user)),rfl,?_,?_⟩
  · intro i
    fin_cases i <;> simp [G,E,D,transposeStacks,Function.update_apply,bank.injective.eq_iff,empty]
  · intro j h₄ h₇
    by_cases h : j = bank 3
    · subst j; simp [empty]
    · simp [G,E,D,Function.update_of_ne h,Function.update_of_ne h₄,Function.update_of_ne h₇]

theorem inputCounters_cost_le {B K : ℕ} (hb : 0 < B) (hk : 0 < K) :
    B.size*(12*(B.size+K.size)+20)+30*(B.size+K.size)+11*K.size+8*(K+B*K)+50 ≤ 217*(B*K) := by
  have b := Nat.le_mul_of_pos_right B hk
  have k := Nat.le_mul_of_pos_left K hb
  have digits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  have sq : B.size*B.size ≤ 4*(B*K) := by
    simpa only [pow_two] using (Cover.Fallback.size_square_le B hb).trans (Nat.mul_le_mul_left 4 b)
  have cross := Nat.mul_le_mul (digits B) (digits K)
  have pos := Nat.mul_pos hb hk
  nlinarith only [sq,cross,(digits B).trans b,(digits K).trans k,k,pos]

end IntegerMultBounds.MathlibTM2.M6.BitNode.OrdinaryHandoff
