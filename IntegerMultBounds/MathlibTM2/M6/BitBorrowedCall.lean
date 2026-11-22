module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedHelper

/-! Run the borrowed invocation on the permanent owner tapes of the packing program. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)

theorem ownerStage_fan_exec {V k T Q : ℕ} {P U : Type}
    (stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)))
    (bank : Fin stage.tapes ↪ Fin T) (fan : Fin (k+2) ↪ Fin T)
    (shared : ∀ i, bank (stage.slots i) = fan (i.castAdd 2))
    (apart : ∀ j : Fin 2, ∀ i, bank i ≠ fan (j.natAdd k))
    (fits : stage.states ≤ Q) (body : P → Pr P T Q prime U) (data : Fin k → Fin V → ZMod 2)
    (u : HS T Q prime U) (S : Stacks T prime)
    (ready : ChartPrivateReady stage (embStk bank S)) (rep : HelperFan fan data S) :
    ∃ z F m, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program fits)))
        (mk u S) m (mk z F) ∧ m ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
      HelperFan fan (stage.transform data) F ∧
      ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  have encoded (x : Fin k → Fin V → ZMod 2) (j : Fin k) : SparseRoleCircuit.encoded (a := prime) x j = fun i => SparseRoleCircuit.encode (x j i) := rfl
  have owners : RepT (phaseOwners data) (embStk (bank ∘ stage.slots) S).L (embStk (bank ∘ stage.slots) S).R := by
    intro i z
    simpa only [phaseOwners,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
      encoded,shared] using rep (i.castAdd 2) z
  obtain ⟨z,F,m,exec,cost,user,_,out,_,off⟩ := ownerStage_exec_emb stage bank fits body data u S ready owners
  refine ⟨z,F,m,exec,cost,user,?_,off⟩
  intro i
  refine Fin.addCases (fun i h => ?_) (fun j h => ?_) i
  · simpa only [phaseOwners,PointwiseRoleGate.bank,Tapes.append,Fin.addCases_left,embStk,Function.comp_apply,
      encoded,shared] using out i h
  · obtain ⟨left,right⟩ := off _ (apart j)
    simpa only [PointwiseRoleGate.bank,Tapes.append,Fin.addCases_right,embStk,Function.comp_apply,left,right]
      using rep (j.natAdd k) h

/-- Reserve two control tapes beyond the actual stage, and use its existing
payload slots as the owner tapes of the packing program. -/
def stageFan {k t : ℕ} (slots : Fin k ↪ Fin t) : Fin (k+2) ↪ Fin (t+2) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((slots.sumMap (Function.Embedding.refl (Fin 2))).trans finSumFinEquiv.toEmbedding)

theorem borrowedCall_exec [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5)
    (w B K : ℕ) (hw : 0 < w) (hb : 0 < B) (hk : 0 < K) (engine : CopyTranspose := CopyTranspose.original) :
    let blocks := (prime^w)^112*B
    let V := (prime^w)^16*(blocks*prime^(64*(w*64))*K)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      let bank := Fin.castAddEmb 2 (n := stage.tapes)
      let fan := stageFan ⟨stage.slots,stage.slots_injective⟩
      ∀ {P U : Type} {Q : ℕ} (fits : stage.states ≤ Q) (body : P → Pr P (stage.tapes+2) Q prime U)
        data u S, ChartPrivateReady stage (embStk bank S) → HelperFan fan data S →
      ∃ z F m out, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program fits)))
        (mk u S) m (mk z F) ∧ m ≤ stage.cost*(stage.tapes+5)+6 ∧ z.user = u.user ∧
        HelperFan fan out F ∧ BorrowedStep n w blocks K p data out := by
  intro blocks V
  have positive : 0 < blocks := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hb
  obtain ⟨_,build⟩ := borrowedInvocation_stage n p.1 p.2 engine
  obtain ⟨stage,_,act,off⟩ := build w blocks K hw positive hk
  refine ⟨stage,?_⟩
  intro bank fan P U Q fits body data u S ready rep
  have shared (i) : bank (stage.slots i) = fan (i.castAdd 2) := by simp [fan,bank,stageFan,@finSumFinEquiv_symm_apply_castAdd 142081 2]
  have apart (j : Fin 2) (i) : bank i ≠ fan (j.natAdd 142081) := by
    simp [bank,fan,stageFan,@finSumFinEquiv_symm_apply_natAdd 142081 2]
    intro eq
    have h := congrArg Fin.val eq
    change i.val = stage.tapes+j.val at h
    omega
  obtain ⟨z,F,m,exec,paid,user,done,_⟩ := ownerStage_fan_exec stage bank fan shared apart fits body data u S ready rep
  exact ⟨z,F,m,stage.transform data,exec,paid,user,done,act data,off data⟩

open RecursiveInterchangeLayout (volume) in
/-- The two chart passes surrounding allocated COPY can be hosted separately.
Their interpreter overhead is uniform in the width and does not involve a
recursive call. -/
theorem borrowedChart_host [M8.Machine.Net] (n : Fin 9) (p : Fin 32 × Fin 5) (enter : Bool) :
    ∃ C : ℝ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
      (∀ x (i : Fin 661), let A := registerChart w n i.val
        Cover.LabelPermutation.Transport v B w (fun g => g*(if enter then A.transpose else A))
          (M8.RevMachine.ext (x (ownerTape n p.1 p.2 i)))
          (M8.RevMachine.ext (stage.transform x (ownerTape n p.1 p.2 i)))) ∧
      (∀ x k, (∀ i, ownerTape n p.1 p.2 i ≠ k) → stage.transform x k = x k) ∧
      ∀ {P U : Type} {T Q : ℕ} (bank : Fin stage.tapes ↪ Fin T) (fan : Fin (142081+2) ↪ Fin T),
        (∀ i, bank (stage.slots i) = fan (i.castAdd 2)) →
        (∀ j : Fin 2, ∀ i, bank i ≠ fan (j.natAdd 142081)) →
        ∀ (fits : stage.states ≤ Q) (body : P → Pr P T Q prime U) data u S,
        (∀ j, (∀ i, stage.slots i ≠ j) → ∀ h, stage.metadata.tape j h =
          readAt blank (S.L (bank j)) (S.R (bank j)) (h-stage.metadata.head j)) →
        HelperFan fan data S →
        ∃ z F m, Exec body (embProg bank (Empty.elim : Empty → P) (foreign (liftQ stage.program fits)))
          (mk u S) m (mk z F) ∧ (m : ℝ) ≤ C*V*(w : ℝ)^M8.Machine.BudgetBound.tau ∧
          z.user = u.user ∧ HelperFan fan (stage.transform data) F ∧
          ∀ j, (∀ i, bank i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨coeff,tapes,build⟩ := borrowedRoute_fixed n p.1 p.2 enter
  let factor := tapes+5
  obtain ⟨C,bound⟩ := labelRoute_cost_bound ((coeff+661)*factor+6) (661*252*factor)
  refine ⟨C,?_⟩
  intro w B K hw hb hk v V
  obtain ⟨stage,count,bill,reads,off⟩ := build w B K hw hb hk
  refine ⟨stage,reads,off,?_⟩
  intro P U T Q bank fan shared apart fits body data u S ready rep
  have same : @phaseOwners 142081 V = copyOwners (v := v) := by
    funext x
    apply congrArg₂ Tapes.mk
    · rfl
    · funext j
      exact (sourceWord_cast (v := v) rfl (x j)).symm
  have host := @ownerStage_fan_exec V 142081 T Q P U
  unfold ChartPrivateReady at host
  rw [same] at host
  obtain ⟨z,F,m,exec,paid,user,done,keep⟩ := host stage bank fan shared apart fits body data u S ready rep
  refine ⟨z,F,m,exec,le_trans ?_ (bound V w hw),user,done,keep⟩
  have pos : 1 ≤ V := by
    change 0 < V
    dsimp [V,v,copyLabelLayout,volume]
    have := Shared50ModularControl.prime_prime.pos
    positivity
  rw [count] at paid
  have time := paid.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (tapes+5) bill) 6)
  change m ≤ (coeff*V+661*(252*LeafCore.coreCost V (w*64)+1))*factor+6 at time
  exact_mod_cast (show m ≤ ((coeff+661)*factor+6)*V+661*252*factor*LeafCore.coreCost V (w*64) by
    have scale := Nat.mul_le_mul_left (661*factor+6) pos
    ring_nf at time scale ⊢
    omega)

end IntegerMultBounds.MathlibTM2.M6.BitNode
