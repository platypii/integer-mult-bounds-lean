module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineBankState

/-! # Raw scalar setup instantiated in the fixed 640-tape forward layout -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def scalarInput (i : Fin 5) : Fin 640 := ⟨533 + i.val, by omega⟩
def wordWidth : Fin 640 := 538

theorem scalarInput_inj : Function.Injective scalarInput := by
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  simp only [scalarInput] at hv
  omega

theorem source_scalar (r : TblR 16) (i : Fin 5) : source r ≠ scalarInput i := by
  intro h
  have hb := bank_range (ForwardBankPlacement.source r)
  have hv := congrArg Fin.val h
  change (bankTape (ForwardBankPlacement.source r)).val = (scalarInput i).val at hv
  simp only [scalarInput] at hv
  omega

theorem source_width (r : TblR 16) : source r ≠ wordWidth := by
  intro h
  have hb := bank_range (ForwardBankPlacement.source r)
  have hv := congrArg Fin.val h
  change (bankTape (ForwardBankPlacement.source r)).val = 538 at hv
  omega

def bankSetup : Pr P 640 Q A U := chirpForwardRawSetup source scalarInput wordWidth consumers

/-- The initial fixed scalar input supplies raw p,α,s,t words and a width counter, with no live bank. -/
theorem bankSetup_exec (W b p α s t : ℕ) (hbW : b ≤ W)
    (hfit : ∀ i : Fin 4, (![p, α, s, t] : Fin 4 → ℕ) i < 2 ^ b)
    (hp0 : 1 ≤ p) (hα0 : 1 ≤ α) (hαp : α ^ 2 ≤ p) (ht0 : 1 ≤ t)
    (hroom : 125 * p < 2 ^ W)
    (v : HS 640 Q A U) (S : Stacks 640 A) (hw : (S.R wordWidth).length = W)
    (hwords : ∀ i : Fin 4, S.R (scalarInput i.castSucc) = binSyms b ((![p, α, s, t] : Fin 4 → ℕ) i))
    (hzero : S.R (scalarInput 4) = []) (hblank : ∀ r, S.R (source r) = [])
    (hconsumers : ∀ b ∈ consumers, ∀ r, S.R (b.rg r) = []) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    ∃ v' S' z n, v'.user = v.user ∧
      n ≤ (100 * W + 8 * b + 137) +
        ((((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) + 5) * tblC W 0 +
          ((2 + (6 * w + 11 * W + 6)) + chirpBankFamilyCost source W w consumers)) ∧
      Exec body (bankSetup) (mk v S) n (mk v' S') ∧
      tblHolds source S' (tblRho W (List.replicate W tick) (List.replicate w tick) z) ∧
      (∀ b ∈ consumers, tblHolds b.rg S'
        (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) ∧
      (z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 7 = chirpBlockCount t m ∧
        z.val 8 = l ∧ z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = q + l + Γ + 5 ∧
        z.val 12 = p + l + Γ + 5 ∧ z.val 13 = 0 ∧ z.val 14 = s ∧ z.val 15 = t ∧
        z.acc = [] ∧ ∀ i, z.val i < 2 ^ W) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → S'.R k = S.R k) := by
  exact chirpForwardRawSetup_exec (body := body) source source_inj scalarInput scalarInput_inj wordWidth
    source_scalar source_width consumers consumers_inj consumers_source consumers_pairwise
    W b p α s t hbW hfit hp0 hα0 hαp ht0 hroom v S hw hwords hzero hblank hconsumers

/-- Every consumer role remains inside the previously allocated table range. -/
theorem consumer_range (b : ChirpBankTarget 16 640) (hb : b ∈ consumers) (r : TblR b.vars) :
    176 ≤ (b.rg r).val ∧ (b.rg r).val < 369 := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
  exact bank_range (c.rg r)

/-- The bank-setup spectator frame covers all arithmetic, product and raw-line workspace. -/
theorem outside_banks (k : Fin 640) (hk : k.val < 176 ∨ 369 ≤ k.val) :
    (∀ r, k ≠ source r) ∧ (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) := by
  constructor
  · intro r h
    have hb := bank_range (ForwardBankPlacement.source r)
    have hv := congrArg Fin.val h
    change k.val = (bankTape (ForwardBankPlacement.source r)).val at hv
    omega
  · intro b hb r h
    have hr := consumer_range b hb r
    have hv := congrArg Fin.val h
    omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
