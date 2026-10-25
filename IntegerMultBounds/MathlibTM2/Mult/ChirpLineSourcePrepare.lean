module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineBankState
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardCallerSize

/-! # Feed computed source words directly to the complete fixed-line preparation -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

/-- Computed source semantics supply every table, multiplier and counter-bank condition. -/
theorem prepare_from_source (s t α p : ℕ) (hst : s < t) (hp : 1 ≤ p) (hα : 1 ≤ α)
    (hαp : α ^ 2 ≤ p) (ht : 1 ≤ t) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let M := chirpBlockCount t m
    let B := chirpForwardCallerBase s t p
    let W := chirpForwardTableWord q B
    ∀ (σ : Fin 16 → ℕ),
    (σ 0 = p ∧ σ 1 = α ∧ σ 5 = m ∧ σ 7 = M ∧ σ 8 = l ∧ σ 9 = Γ ∧
      σ 10 = q ∧ σ 11 = w ∧ σ 13 = 0 ∧ σ 14 = s ∧ σ 15 = t ∧ ∀ i, σ i < 2 ^ W) →
    ∀ (v : HS 640 Q A U) (S : Stacks 640 A),
    (∀ b ∈ consumers, tblHolds b.rg S (tblRho W (List.replicate W tick) (List.replicate w tick)
      ⟨fun i => σ (b.index i), []⟩)) →
    ∃ v' n, v'.user = v.user ∧
      n ≤ (3 * chirpMultiplierSetupCost W w q w +
        (chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true +
          chirpOutputFactorSetupCost W w q Γ m)) + countersCost W p q l Γ w t ∧
      Exec body prepare (mk v S) n (mk v' { S with R :=
        (countersR p q l Γ w t (tablesR w q s t α m M Γ (readinessR q w S.R))) }) := by
  dsimp only
  intro σ ⟨hσp, hσα, hσm, hσM, hσl, hσΓ, hσq, hσw, hσ0, hσs, hσt, hσfit⟩ v S hbanks
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let B := chirpForwardCallerBase s t p
  let W := chirpForwardTableWord q B
  change σ 5 = m at hσm
  change σ 7 = chirpBlockCount t m at hσM
  change σ 8 = l at hσl
  change σ 9 = Γ at hσΓ
  change σ 10 = q at hσq
  change σ 11 = q + l + Γ + 5 at hσw
  change ∀ i, σ i < 2 ^ W at hσfit
  rcases chirpForwardCaller_fits s t p α hp hαp with
    ⟨_, _, h125, hwW, hsB, htB, hαB, hmB, _, _, _, _, hcrop, _, _, _, hroom⟩
  have h125W : 125 * p < 2 ^ W := h125
  have hbase : t + 125 * p ≤ B := le_max_right _ _
  have hB : 1 ≤ B := by omega
  have hq : 13 ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hw1 : 1 ≤ q + l + Γ + 5 := by omega
  have hΓq : Γ ≤ q := by dsimp [q, Γ, chirpForwardPrecision, chirpForwardGrowth]; omega
  have hqΓ : 13 ≤ q - Γ := by dsimp [q, Γ, chirpForwardPrecision, chirpForwardGrowth]; omega
  have hqW : q < W := by dsimp [W, chirpForwardTableWord]; omega
  have hαW : 2 * α < 2 ^ W := by
    have hαp' : α ≤ p := (Nat.le_mul_self α).trans (by simpa only [pow_two] using hαp)
    omega
  have hpq : p ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  rcases chirpForwardCaller_tableBounds s t p α hp ht hαp with ⟨hMB, hprod, hshape⟩
  have hm0 : 1 ≤ m := by
    change 1 ≤ α * (Nat.sqrt p + 1)
    exact Nat.mul_le_mul hα (by omega : 1 ≤ Nat.sqrt p + 1)
  rcases consumer_state W (q + l + Γ + 5) σ S hbanks with ⟨_, _, hdim, hmul, hcoef⟩
  rw [hσp, hσq, hσl, hσΓ, hσw, hσt, hσ0] at hdim
  rw [hσq, hσw, hσ0] at hmul
  have hdimfit : ∀ i : Fin 6, (![p, q, l, Γ, q + l + Γ + 5, t] : Fin 6 → ℕ) i < 2 ^ W := by
    intro i
    fin_cases i
    · exact hσp ▸ hσfit 0
    · change q < 2 ^ W; exact hσq ▸ hσfit 10
    · change l < 2 ^ W; exact hσl ▸ hσfit 8
    · change Γ < 2 ^ W; exact hσΓ ▸ hσfit 9
    · exact hσw ▸ hσfit 11
    · exact hσt ▸ hσfit 15
  exact prepare_exec (body := body) W (q + l + Γ + 5) q s t α m (chirpBlockCount t m) Γ B p l
    hwW hw1 hroom hpq (by rfl) hcrop (chirpForwardTableWord_size q B hq hB)
    hΓq hqΓ hqW hαW hst.le hsB htB hαB hmB hMB hprod hm0 hshape (by omega) (by omega)
    (fun b hb => chirpForwardWindow_machineGate s t α p l b hst.le hp hb)
    (coefficientState σ) hσq hσs hσt hσα hσm hσM hσΓ
    (coefficientState_owned σ hσ0) hσ0 hσ0 hσ0 hσ0 (coefficientState_fit W σ hσfit)
    rfl v S hcoef hmul hdim hdimfit

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
