module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankClear
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankFamily

/-! # Release a structural family of disjoint generated table banks -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem chirpBankClearR_off (rg : TblR n → Fin T) (R : Regs T A) (k : Fin T)
    (hk : ∀ r, k ≠ rg r) : chirpBankClearR rg R k = R k := by
  have hv : k ∉ List.ofFn (fun i => rg (.v i)) := by
    intro h
    obtain ⟨i, he⟩ := List.mem_ofFn.mp h
    exact hk (.v i) he.symm
  simp [chirpBankClearR, hk .wr, hk .wn, hv]

def chirpBankFamilyClear : List (ChirpBankTarget n T) → Pr P T Q A U
  | [] => .act .done
  | b :: bs => .seq (chirpBankClear b.rg) (chirpBankFamilyClear bs)

def chirpBankFamilyClearR : List (ChirpBankTarget n T) → Regs T A → Regs T A
  | [], R => R
  | b :: bs, R => chirpBankFamilyClearR bs (chirpBankClearR b.rg R)

def chirpBankFamilyClearCost (W e : ℕ) : List (ChirpBankTarget n T) → ℕ
  | [] => 1
  | b :: bs => (2 * (b.vars * W) + 2 * b.vars + 1 + (2 * (W + e) + 5)) + chirpBankFamilyClearCost W e bs

/-- Registers outside all allocated bank roles are preserved by the entire release. -/
theorem chirpBankFamilyClearR_off (bs : List (ChirpBankTarget n T)) (R : Regs T A) (k : Fin T)
    (hk : ∀ b ∈ bs, ∀ r, k ≠ b.rg r) : chirpBankFamilyClearR bs R k = R k := by
  induction bs generalizing R with
  | nil => rfl
  | cons b bs ih =>
    rw [chirpBankFamilyClearR, ih _ (fun c hc => hk c (List.mem_cons_of_mem _ hc))]
    exact chirpBankClearR_off b.rg R k (hk b (by simp))

/-- All generated variables and headers are erased with exact symbol cost and every bank role ends empty. -/
theorem chirpBankFamilyClear_exec (bs : List (ChirpBankTarget n T))
    (hinj : ∀ b ∈ bs, Function.Injective b.rg)
    (hpair : bs.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s))
    (W e : ℕ) (σ : Fin n → ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hS : ∀ b ∈ bs, tblHolds b.rg S (tblRho W (List.replicate W tick) (List.replicate e tick)
      ⟨fun i => σ (b.index i), []⟩)) :
    ∃ v', v'.user = v.user ∧
      Exec body (chirpBankFamilyClear bs) (mk v S) (chirpBankFamilyClearCost W e bs)
        (mk v' { S with R := chirpBankFamilyClearR bs S.R }) ∧
      (∀ b ∈ bs, ∀ r, chirpBankFamilyClearR bs S.R (b.rg r) = []) := by
  induction bs generalizing v S with
  | nil => exact ⟨v, rfl, Exec.act (body := body) .done (mk v S), by simp⟩
  | cons b bs ih =>
    have hp := List.pairwise_cons.mp hpair
    have hhead := hS b (by simp)
    obtain ⟨v₁, hu₁, he₁⟩ := chirpBankClear_exec (body := body) b.rg (hinj b (by simp)) W e
      (List.replicate W tick) (List.replicate e tick) (by simp) (by simp)
      ⟨fun i => σ (b.index i), []⟩ v S hhead
    let S₁ : Stacks T A := { S with R := chirpBankClearR b.rg S.R }
    have htail : ∀ c ∈ bs, tblHolds c.rg S₁
        (tblRho W (List.replicate W tick) (List.replicate e tick) ⟨fun i => σ (c.index i), []⟩) := by
      intro c hc r
      exact (chirpBankClearR_off b.rg S.R _ (fun s => (hp.1 c hc s r).symm)).trans
        (hS c (List.mem_cons_of_mem _ hc) r)
    obtain ⟨v₂, hu₂, he₂, hz₂⟩ := ih (fun c hc => hinj c (List.mem_cons_of_mem _ hc)) hp.2 v₁ S₁ htail
    refine ⟨v₂, hu₂.trans hu₁, Exec.seq he₁ he₂, ?_⟩
    intro c hc r
    rcases List.mem_cons.mp hc with he | hc
    · subst c
      rw [chirpBankFamilyClearR, chirpBankFamilyClearR_off bs _ _ (fun c hc s => hp.1 c hc r s)]
      exact chirpBankClear_empty b.rg (hinj b (by simp)) W (List.replicate W tick)
        (List.replicate e tick) ⟨fun i => σ (b.index i), []⟩ S hhead rfl r
    · exact hz₂ c hc r

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
