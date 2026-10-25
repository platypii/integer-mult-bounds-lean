module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineReadiness
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTablePair
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardTableSize

/-! # Generate all four retained coefficient streams for the fixed line

One coefficient bank is reused for G,K,E and normalization. The program restores
that bank and changes only the four table destinations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

theorem coefficient_inj : Function.Injective coefficient :=
  bankTape_inj.comp (ForwardBankPlacement.place_injective _ (by decide))

theorem bank_ports (i : Fin 193) :
    bankTape i ≠ processor .ys ∧ bankTape i ≠ batch .srcY ∧
      bankTape i ≠ output.cr .ys ∧ bankTape i ≠ output.nr .ys := by
  have hb := bank_range i
  have hp := processor_range .ys
  have hc : (output.cr .ys).val < 146 := (OutputPlacement.layout.cr .ys).isLt
  have hn : (output.nr .ys).val < 146 := (OutputPlacement.layout.nr .ys).isLt
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    intro h
    have hv := congrArg Fin.val h
    first | omega | (simp only [batch, Function.comp_apply, productTape, Fixed.batchReg] at hv; omega)

theorem coefficient_ports (r : TblR 48) :
    coefficient r ≠ processor .ys ∧ coefficient r ≠ batch .srcY ∧
      coefficient r ≠ output.cr .ys ∧ coefficient r ≠ output.nr .ys := bank_ports _

def tables : Pr P 640 Q A U :=
  .seq (chirpTablePair coefficient (processor .ys) (batch .srcY))
    (chirpOutputFactorSetup coefficient (output.cr .ys) (output.nr .ys))

def tablesR (w q s t α m M Γ : ℕ) (R : Regs 640 A) : Regs 640 A :=
  Function.update (Function.update (Function.update (Function.update R
    (processor .ys) (chirpScheduledStream A w q s t α m M false ++ R (processor .ys)))
    (batch .srcY) (chirpScheduledStream A w q s t α m M true ++ R (batch .srcY)))
    (output.cr .ys) (cstream A w ((chirpOutputFactors s t α q Γ m).map fun e => (⟨e, 0⟩ : GaussianInt)) ++ R (output.cr .ys)))
    (output.nr .ys) (csyms A w (⟨(chirpNormalization q α : ℤ), 0⟩ : GaussianInt) ++ R (output.nr .ys))

/-- All non-table registers are retained, for composing this setup with the fixed line. -/
theorem tables_off (w q s t α m M Γ : ℕ) (R : Regs 640 A) (k : Fin 640)
    (hG : k ≠ processor .ys) (hK : k ≠ batch .srcY)
    (hE : k ≠ output.cr .ys) (hN : k ≠ output.nr .ys) :
    tablesR w q s t α m M Γ R k = R k := by
  simp only [tablesR, Function.update_of_ne hN, Function.update_of_ne hE,
    Function.update_of_ne hK, Function.update_of_ne hG]

/-- All four table streams are produced once; the coefficient evaluator bank is restored. -/
theorem tables_exec (W w q s t α m M Γ B : ℕ) (hwW : w ≤ W)
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
    (hS : tblHolds coefficient S (tblRho W (List.replicate W tick) (List.replicate w tick) st)) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true +
        chirpOutputFactorSetupCost W w q Γ m ∧
      Exec body tables (mk v S) n (mk v' { S with R := tablesR w q s t α m M Γ S.R }) := by
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpTablePair_exec (body := body) coefficient_inj
    (processor .ys) (batch .srcY) (by decide +kernel)
    (fun r => (coefficient_ports r).1) (fun r => (coefficient_ports r).2.1)
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW st size s t α m M
    hq hs ht hα hm hM hst hsB htB hαB hMB hprod hm0 hshape howned h37 h38 h42 h44 hfit hacc v S hS
  let S₁ : Stacks 640 A := { S with R := (Function.update
    (Function.update S.R (processor .ys) (chirpScheduledStream A w q s t α m M false ++ S.R (processor .ys)))
    (batch .srcY) (chirpScheduledStream A w q s t α m M true ++ S.R (batch .srcY))) }
  have hb : tblHolds coefficient S₁ (tblRho W (List.replicate W tick) (List.replicate w tick) st) := by
    intro r
    simpa only [S₁, Function.update_of_ne (coefficient_ports r).1,
      Function.update_of_ne (coefficient_ports r).2.1] using hS r
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpOutputFactorSetup_exec (body := body) coefficient_inj
    (output.cr .ys) (output.nr .ys) (by decide +kernel)
    (fun r => (coefficient_ports r).2.2.1) (fun r => (coefficient_ports r).2.2.2)
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW st
    (size.lowerPrecision hqΓ (Nat.sub_le q Γ)) s t α m hq hΓ hΓq hs ht hα hm h44 hqW hαW
    hst hsB htB hαB hmB ht0 hα0 hgate howned hfit hacc v₁ S₁ hb
  refine ⟨v₂, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂, ?_⟩
  simpa only [tables, tablesR, S₁,
    Function.update_of_ne (show output.cr .ys ≠ batch .srcY by decide +kernel),
    Function.update_of_ne (show output.cr .ys ≠ processor .ys by decide +kernel),
    Function.update_of_ne (show output.nr .ys ≠ batch .srcY by decide +kernel),
    Function.update_of_ne (show output.nr .ys ≠ processor .ys by decide +kernel)] using Exec.seq he₁ he₂

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
