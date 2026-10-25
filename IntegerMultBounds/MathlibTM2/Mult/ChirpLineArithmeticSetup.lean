module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineTables

/-! # Compose fixed-line multiplier readiness and retained coefficient generation -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def arithmeticSetup : Pr P 640 Q A U := .seq readiness tables

/-- The readiness stage preserves the coefficient bank used by all subsequent tables. -/
theorem readiness_coefficient (q w : ℕ) (R : Regs 640 A) (i : TblR 48) :
    readinessR q w R (coefficient i) = R (coefficient i) :=
  readiness_off q w R _ (fun r _ => bank_processor _ r)
    (fun r _ => (bank_output _ r).1) (fun r _ => (bank_output _ r).2)

/-- One executed setup charges readiness and all tables once, preserving both binary banks. -/
theorem arithmeticSetup_exec (W w q s t α m M Γ B : ℕ) (hwW : w ≤ W)
    (hw1 : 1 ≤ w) (hroom : 4 * w + 2 < 2 ^ W)
    (size : ChirpTableSize W q B) (hΓq : Γ ≤ q) (hqΓ : 13 ≤ q - Γ)
    (hqW : q < W) (hαW : 2 * α < 2 ^ W) (hst : s ≤ t)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hmB : m ≤ B)
    (hMB : M ≤ B) (hprod : M * m ≤ B) (hm0 : 1 ≤ m) (hshape : 4 * m + 1 ≤ B)
    (ht0 : 0 < t) (hα0 : 0 < α)
    (hgate : ∀ b < m, 4 * chirpEN s t b ≤ (q - Γ - 1) * chirpED t α)
    (st : TblSt 48 A) (hq : st.val 19 = q) (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hα : st.val 36 = α) (hm : st.val 45 = m) (hM : st.val 43 = M) (hΓ : st.val 46 = Γ)
    (howned : ∀ i ∈ chirpTableOwned, st.val i = 0)
    (h37 : st.val 37 = 0) (h38 : st.val 38 = 0) (h42 : st.val 42 = 0) (h44 : st.val 44 = 0)
    (hfit : ∀ i, st.val i < 2 ^ W) (hacc : st.acc = [])
    (v : HS 640 Q A U) (S : Stacks 640 A)
    (hS : tblHolds coefficient S (tblRho W (List.replicate W tick) (List.replicate w tick) st))
    (hMulBank : tblHolds multiplier S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨![q, w, 0, 0, 0], []⟩)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 3 * chirpMultiplierSetupCost W w q w +
        (chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true +
        chirpOutputFactorSetupCost W w q Γ m) ∧
      Exec body arithmeticSetup (mk v S) n (mk v' { S with R := tablesR w q s t α m M Γ (readinessR q w S.R) }) := by
  have hqfit : q < 2 ^ W := by rw [← hq]; exact hfit 19
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := readiness_exec (body := body) W q w hw1 hwW hroom hqfit v S hMulBank
  let S₁ : Stacks 640 A := { S with R := readinessR q w S.R }
  have hb : tblHolds coefficient S₁ (tblRho W (List.replicate W tick) (List.replicate w tick) st) := by
    intro i
    exact (readiness_coefficient q w S.R i).trans (hS i)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := tables_exec (body := body) W w q s t α m M Γ B hwW
    size hΓq hqΓ hqW hαW hst hsB htB hαB hmB hMB hprod hm0 hshape ht0 hα0 hgate
    st hq hs ht hα hm hM hΓ howned h37 h38 h42 h44 hfit hacc v₁ S₁ hb
  exact ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
