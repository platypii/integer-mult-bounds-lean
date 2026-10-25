module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardConsumerSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardSourceLoad

/-! # Set up the forward scalar and consumer banks from original binary words -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpForwardRawSetup (src : TblR 16 → Fin T) (raw : Fin 5 → Fin T) (width : Fin T)
    (bs : List (ChirpBankTarget 16 T)) : Pr P T Q A U :=
  .seq (chirpForwardSourceLoad src raw width) (chirpForwardConsumerSetup src bs)

/-- One executed setup starts from raw p,α,s,t words, with no initialized table bank. -/
theorem chirpForwardRawSetup_exec (src : TblR 16 → Fin T) (hsrc : Function.Injective src)
    (raw : Fin 5 → Fin T) (hraw : Function.Injective raw) (width : Fin T)
    (hrawSep : ∀ r i, src r ≠ raw i) (hwidth : ∀ r, src r ≠ width)
    (bs : List (ChirpBankTarget 16 T)) (hinj : ∀ b ∈ bs, Function.Injective b.rg)
    (hsep : ∀ b ∈ bs, ∀ r s, b.rg r ≠ src s)
    (hpair : bs.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s))
    (W b p α s t : ℕ) (hbW : b ≤ W)
    (hfit : ∀ i : Fin 4, (![p, α, s, t] : Fin 4 → ℕ) i < 2 ^ b)
    (hp0 : 1 ≤ p) (hα0 : 1 ≤ α) (hαp : α ^ 2 ≤ p) (ht0 : 1 ≤ t)
    (hroom : 125 * p < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hw : (S.R width).length = W)
    (hwords : ∀ i : Fin 4, S.R (raw i.castSucc) = binSyms b ((![p, α, s, t] : Fin 4 → ℕ) i))
    (hzero : S.R (raw 4) = []) (hblank : ∀ r, S.R (src r) = [])
    (hconsumers : ∀ b ∈ bs, ∀ r, S.R (b.rg r) = []) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    ∃ v' S' z n, v'.user = v.user ∧
      n ≤ (100 * W + 8 * b + 137) +
        ((((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) + 5) * tblC W 0 +
          ((2 + (6 * w + 11 * W + 6)) + chirpBankFamilyCost src W w bs)) ∧
      Exec body (chirpForwardRawSetup src raw width bs) (mk v S) n (mk v' S') ∧
      tblHolds src S' (tblRho W (List.replicate W tick) (List.replicate w tick) z) ∧
      (∀ b ∈ bs, tblHolds b.rg S'
        (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) ∧
      (z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 7 = chirpBlockCount t m ∧
        z.val 8 = l ∧ z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = q + l + Γ + 5 ∧
        z.val 12 = p + l + Γ + 5 ∧ z.val 13 = 0 ∧ z.val 14 = s ∧ z.val 15 = t ∧
        z.acc = [] ∧ ∀ i, z.val i < 2 ^ W) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ k, (∀ r, k ≠ src r) → (∀ b ∈ bs, ∀ r, k ≠ b.rg r) → S'.R k = S.R k) := by
  dsimp only
  obtain ⟨v₁, R₁, n₁, hu₁, hn₁, he₁, hS₁, hoff₁⟩ := chirpForwardSourceLoad_exec (body := body)
    src hsrc raw hraw width hrawSep hwidth W b p α s t hbW hfit v S hw hwords hzero hblank
  let st : TblSt 16 A := ⟨ForwardParameters.sourceValues p α s t, []⟩
  let S₁ : Stacks T A := { S with R := R₁ }
  have hstfit : ∀ i, st.val i < 2 ^ W := by
    intro i
    dsimp only [st, ForwardParameters.sourceValues]
    have hf (j : Fin 5) : (![p, α, s, t, 0] : Fin 5 → ℕ) j < 2 ^ W := by
      fin_cases j
      all_goals first
        | exact (hfit 0).trans_le (Nat.pow_le_pow_right (by decide) hbW)
        | exact (hfit 1).trans_le (Nat.pow_le_pow_right (by decide) hbW)
        | exact (hfit 2).trans_le (Nat.pow_le_pow_right (by decide) hbW)
        | exact (hfit 3).trans_le (Nat.pow_le_pow_right (by decide) hbW)
        | simp
    exact hf _
  obtain ⟨v₂, S₂, z, n₂, hu₂, hn₂, he₂, hzsrc, hzbanks, hz, hframe⟩ :=
    chirpForwardConsumerSetup_exec (body := body) src hsrc bs hinj hsep hpair W 0
      (List.replicate W tick) [] (by simp) rfl (Nat.zero_le W) st p α s t
      (by simp [st, ForwardParameters.sourceValues, ForwardParameters.sourceIndex])
      (by simp [st, ForwardParameters.sourceValues, ForwardParameters.sourceIndex])
      (by simp [st, ForwardParameters.sourceValues, ForwardParameters.sourceIndex])
      (by simp [st, ForwardParameters.sourceValues, ForwardParameters.sourceIndex])
      (by simp [st, ForwardParameters.sourceValues, ForwardParameters.sourceIndex])
      hp0 hα0 hαp ht0 hroom hstfit v₁ S₁ hS₁
      (fun b hb r => (hoff₁ _ (fun r' => hsep b hb r r')).trans (hconsumers b hb r))
  refine ⟨v₂, S₂, z, n₁ + n₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hzsrc, hzbanks,
    hz, hframe.1, hframe.2.1, hframe.2.2.1, ?_⟩
  · rw [hn₁]
    simpa only [Nat.mul_zero, Nat.zero_add] using Nat.add_le_add_left hn₂ (100 * W + 8 * b + 137)
  · intro k hks hkb
    exact (hframe.2.2.2 k hks hkb).trans (hoff₁ k hks)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
