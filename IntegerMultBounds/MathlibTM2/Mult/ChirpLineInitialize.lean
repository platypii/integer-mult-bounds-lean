module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineBankSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpLineSourcePrepare

/-! # One fixed program initializes all retained forward-line setup from raw scalar words -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def initialization : Pr P 640 Q A U := .seq bankSetup prepare

def preparedStack (p q l Γ w t s α m M : ℕ) (S : Stacks 640 A) : Stacks 640 A :=
  { S with R := (countersR p q l Γ w t (tablesR w q s t α m M Γ (readinessR q w S.R))) }

def initializeCost (W b p q l Γ w t m M : ℕ) : ℕ :=
  ((100 * W + 8 * b + 137) +
    ((((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) + 5) * tblC W 0 +
      ((2 + (6 * w + 11 * W + 6)) + chirpBankFamilyCost source W w consumers))) +
  ((3 * chirpMultiplierSetupCost W w q w +
    (chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true +
      chirpOutputFactorSetupCost W w q Γ m)) + countersCost W p q l Γ w t)

/-- Raw scalar bank setup and complete arithmetic preparation execute in one dimension-independent program. -/
theorem initialize_exec (s t α p : ℕ) (hst : s < t) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let M := chirpBlockCount t m
    let B := chirpForwardCallerBase s t p
    let W := chirpForwardTableWord q B
    let b := Nat.size B
    ∀ (v : HS 640 Q A U) (S : Stacks 640 A),
    (S.R wordWidth).length = W →
    (∀ i : Fin 4, S.R (scalarInput i.castSucc) = binSyms b ((![p, α, s, t] : Fin 4 → ℕ) i)) →
    S.R (scalarInput 4) = [] → (∀ r, S.R (source r) = []) →
    (∀ b ∈ consumers, ∀ r, S.R (b.rg r) = []) →
    ∃ v' SB z n, v'.user = v.user ∧ n ≤ initializeCost W b p q l Γ w t m M ∧
      Exec body initialization (mk v S) n (mk v' (preparedStack p q l Γ w t s α m M SB)) ∧
      tblHolds source SB (tblRho W (List.replicate W tick) (List.replicate w tick) z) ∧
      (∀ b ∈ consumers, tblHolds b.rg SB
        (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) ∧
      (z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 7 = M ∧ z.val 8 = l ∧
        z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = w ∧ z.val 13 = 0 ∧ z.val 14 = s ∧
        z.val 15 = t ∧ ∀ i, z.val i < 2 ^ W) ∧ z.acc = [] ∧
      SB.inp = S.inp ∧ SB.out = S.out ∧ SB.L = S.L ∧
      (∀ k, k.val < 176 ∨ 369 ≤ k.val → SB.R k = S.R k) ∧
      (∀ k, (∀ r, k ≠ source r) → (∀ b ∈ consumers, ∀ r, k ≠ b.rg r) → SB.R k = S.R k) := by
  dsimp only
  intro v S hwidth hwords hzero hsource hconsumers
  have hαp' : α ≤ p := (Nat.le_mul_self α).trans (by simpa only [pow_two] using hαp)
  have hp : 1 ≤ p := hα.trans hαp'
  have ht : 1 ≤ t := by omega
  rcases chirpForwardCaller_fits s t p α hp hαp with ⟨hfit, hbW, hroom, _⟩
  obtain ⟨v₁, SB, z, n₁, hu₁, hn₁, he₁, hsrc, hbanks, hz, hframe⟩ :=
    bankSetup_exec (body := body) _ _ p α s t hbW hfit hp hα hαp ht hroom
      v S hwidth hwords hzero hsource hconsumers
  rcases hz with ⟨hzp, hzα, hzm, hzM, hzl, hzΓ, hzq, hzw, _, hz0, hzs, hzt, hzacc, hzfit⟩
  have hvals := And.intro hzp (And.intro hzα (And.intro hzm (And.intro hzM
    (And.intro hzl (And.intro hzΓ (And.intro hzq (And.intro hzw
      (And.intro hz0 (And.intro hzs (And.intro hzt hzfit))))))))))
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := prepare_from_source (body := body) s t α p hst hp hα hαp ht
    z.val hvals v₁ SB hbanks
  refine ⟨v₂, SB, z, n₁ + n₂, hu₂.trans hu₁, Nat.add_le_add hn₁ hn₂, Exec.seq he₁ he₂,
    hsrc, hbanks, hvals, hzacc, hframe.1, hframe.2.1, hframe.2.2.1, ?_, hframe.2.2.2⟩
  intro k hk
  have hoff := outside_banks k hk
  exact hframe.2.2.2 k hoff.1 hoff.2

/-- The raw bank-setup frame carries the initial fresh arithmetic state into preparation. -/
theorem initialized_prepared (p q l Γ w t s α m M : ℕ) (S SB : Stacks 640 A)
    (hL : SB.L = S.L)
    (hframe : ∀ k, k.val < 176 ∨ 369 ≤ k.val → SB.R k = S.R k)
    (hproc : ∀ r, S.R (processor r) = [])
    (hcr : ∀ r, S.R (output.cr r) = []) (hnr : ∀ r, S.R (output.nr r) = [])
    (hclean : CClean output.mul S) (hK0 : S.R (batch .srcY) = [])
    (hbank : ∀ i, S.R (output.bank i) = []) :
    let SF := preparedStack p q l Γ w t s α m M SB
    Ready (fun r => SF.R (processor r)) w q ∧
      SF.R (processor .ys) = chirpScheduledStream A w q s t α m M false ∧
      SF.R (batch .srcY) = chirpScheduledStream A w q s t α m M true ∧
      ChirpOutputState output SF q w [] (chirpOutputFactors s t α q Γ m) (chirpNormalization q α) ∧
      (∀ i, (SF.R (output.dim i)).length = chirpOutputDimensionCount p q l Γ w t i) ∧
      (∀ i : Fin 22, 9 ≤ i.val → SF.R (output.bank i) = []) := by
  have hp (r : CR) : SB.R (processor r) = [] :=
    (hframe _ (Or.inl (processor_range r).2)).trans (hproc r)
  have hc (r : CR) : SB.R (output.cr r) = [] :=
    (hframe _ (Or.inl ((OutputPlacement.layout.cr r).isLt.trans_le (by decide)))).trans (hcr r)
  have hn (r : CR) : SB.R (output.nr r) = [] :=
    (hframe _ (Or.inl ((OutputPlacement.layout.nr r).isLt.trans_le (by decide)))).trans (hnr r)
  have hm : CClean output.mul SB := by
    intro i
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact (hclean i).1
    · exact (hframe _ (Or.inl (show (output.mul i).val < 176 from by
        have hi : (output.mul i).val < 64 := i.isLt
        omega))).trans (hclean i).2
  have hk : SB.R (batch .srcY) = [] :=
    (hframe _ (Or.inr (by decide +kernel))).trans hK0
  have hb (i : Fin 22) : SB.R (output.bank i) = [] :=
    (hframe _ (Or.inl ((OutputPlacement.layout.bank i).isLt.trans_le (by decide)))).trans (hbank i)
  exact prepare_state p q l Γ w t s α m M SB hp hc hn hm hk hb

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
