module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankClone

/-! # Install a finite family of disjoint consumer banks from one source bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

structure ChirpBankTarget (n T : ℕ) where
  vars : ℕ
  rg : TblR vars → Fin T
  index : Fin vars → Fin n

variable {T Q A n : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpBankFamily (src : TblR n → Fin T) : List (ChirpBankTarget n T) → Pr P T Q A U
  | [] => .act .done
  | b :: bs => .seq (chirpBankClone src b.rg b.index) (chirpBankFamily src bs)

def chirpBankFamilyCost (src : TblR n → Fin T) (W e : ℕ) : List (ChirpBankTarget n T) → ℕ
  | [] => 1
  | b :: bs => chirpBankLoadCost b.rg (fun i => src (.v (b.index i))) W e (fun _ => W) +
      chirpBankFamilyCost src W e bs

/-- Every bank receives its assigned variables, with the common source and all spectators kept. -/
theorem chirpBankFamily_exec (src : TblR n → Fin T) (hsrc : Function.Injective src)
    (bs : List (ChirpBankTarget n T))
    (hinj : ∀ b ∈ bs, Function.Injective b.rg)
    (hsep : ∀ b ∈ bs, ∀ r s, b.rg r ≠ src s)
    (hpair : bs.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s))
    (W e : ℕ) (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e)
    (st : TblSt n A) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds src S (tblRho W wl nl st))
    (hblank : ∀ b ∈ bs, ∀ r, S.R (b.rg r) = []) :
    ∃ v' R, v'.user = v.user ∧
      Exec body (chirpBankFamily src bs) (mk v S) (chirpBankFamilyCost src W e bs)
        (mk v' { S with R := R }) ∧
      (∀ b ∈ bs, tblHolds b.rg { S with R := R }
        (tblRho W (List.replicate W tick) (List.replicate e tick) ⟨fun i => st.val (b.index i), []⟩)) ∧
      (∀ k, (∀ b ∈ bs, ∀ r, k ≠ b.rg r) → R k = S.R k) := by
  induction bs generalizing v S with
  | nil => exact ⟨v, S.R, rfl, Exec.act (body := body) .done (mk v S), by simp, by simp⟩
  | cons b bs ih =>
    have hp := List.pairwise_cons.mp hpair
    obtain ⟨v₁, R₁, hu₁, he₁, hb, hoff₁⟩ := chirpBankClone_exec (body := body) src b.rg hsrc
      (hinj b (by simp)) (hsep b (by simp)) b.index W e wl nl hwl hnl st hfit v S hS
      (hblank b (by simp))
    let S₁ : Stacks T A := { S with R := R₁ }
    have hs₁ : tblHolds src S₁ (tblRho W wl nl st) := by
      intro r
      rw [show S₁.R (src r) = S.R (src r) from hoff₁ _ (fun s => (hsep b (by simp) s r).symm)]
      exact hS r
    obtain ⟨v₂, R₂, hu₂, he₂, hbs, hoff₂⟩ := ih
      (fun c hc => hinj c (List.mem_cons_of_mem _ hc))
      (fun c hc => hsep c (List.mem_cons_of_mem _ hc)) hp.2 v₁ S₁ hs₁
      (by
        intro c hc r
        rw [show S₁.R (c.rg r) = S.R (c.rg r) from hoff₁ _ (fun s => (hp.1 c hc s r).symm)]
        exact hblank c (List.mem_cons_of_mem _ hc) r)
    refine ⟨v₂, R₂, hu₂.trans hu₁, Exec.seq he₁ he₂, ?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with he | hc
      · subst c
        intro r
        rw [show ({ S with R := R₂ } : Stacks T A).R (b.rg r) = S₁.R (b.rg r) from
          hoff₂ _ (fun c hc s => hp.1 c hc r s)]
        exact hb r
      · exact hbs c hc
    · intro k hk
      exact (hoff₂ k (fun c hc => hk c (List.mem_cons_of_mem _ hc))).trans
        (hoff₁ k (hk b (by simp)))

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
