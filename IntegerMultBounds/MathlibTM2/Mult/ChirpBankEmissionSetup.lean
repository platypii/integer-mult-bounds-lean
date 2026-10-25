module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! # Generate an evaluator emission-width header from a computed binary variable -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpBankEmissionSetup (rg : TblR n → Fin T) (i : Fin n) : Pr P T Q A U :=
  .seq (uclear (rg .wn)) (toUnary (rg (.v i)) (rg .wn) (rg (.z 0)) (rg (.z 1)) (rg (.z 2)))

/-- Replace the old header by the selected width, retaining all binary variables and scratch. -/
theorem chirpBankEmissionSetup_exec (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) (i : Fin n)
    (hfit : st.val i < 2 ^ W) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) :
    ∃ v' k, v'.user = v.user ∧ k ≤ 2 * nl.length + 2 + (6 * st.val i + 11 * W + 6) ∧
      Exec body (chirpBankEmissionSetup rg i) (mk v S) k
        (mk v' { S with R := Function.update S.R (rg .wn) (List.replicate (st.val i) tick) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body (rg .wn) v S
  rw [hS .wn] at he₁
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg .wn) [] }
  have hreg : [rg (.v i), rg .wn, rg (.z 0), rg (.z 1), rg (.z 2)].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff]
  have hoff (r : TblR n) (hr : r ≠ .wn) : S₁.R (rg r) = S.R (rg r) :=
    Function.update_of_ne (hrg.ne hr) _ _
  obtain ⟨v₂, k, hu₂, hk, he₂⟩ := toUnary_exec_linear body hreg hfit v₁ S₁
    (by rw [hoff (.v i) (by intro h; cases h), hS (.v i)]; rfl)
    (by rw [hoff (.z 0) (by intro h; cases h), hS (.z 0)]; rfl)
    (by rw [hoff (.z 1) (by intro h; cases h), hS (.z 1)]; rfl)
    (by rw [hoff (.z 2) (by intro h; cases h), hS (.z 2)]; rfl)
  refine ⟨v₂, _, hu₂.trans hu₁, Nat.add_le_add_left hk _, ?_⟩
  simpa only [chirpBankEmissionSetup, S₁, Function.update_self, List.append_nil,
    Function.update_idem, tblRho_wn] using Exec.seq he₁ he₂

/-- The generated header establishes the evaluator contract at the computed emission width. -/
theorem chirpBankEmissionSetup_holds (rg : TblR n → Fin T) (hrg : Function.Injective rg)
    (W : ℕ) (wl nl : List (Fin (A + 4))) (st : TblSt n A) (i : Fin n)
    (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st)) :
    tblHolds rg { S with R := Function.update S.R (rg .wn) (List.replicate (st.val i) tick) }
      (tblRho W wl (List.replicate (st.val i) tick) st) := by
  intro r
  cases r <;> simp [hrg.eq_iff, tblRho] at hS ⊢ <;> exact hS _

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
