module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardConsumers
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankEmissionSetup

/-! # Execute scalar selection once and install every forward consumer bank -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpForwardConsumerSetup (src : TblR 16 → Fin T) (bs : List (ChirpBankTarget 16 T)) : Pr P T Q A U :=
  .seq (tblCompile src tblChirpForwardCallerParameters)
    (.seq (chirpBankEmissionSetup src 11) (chirpBankFamily src bs))

/-- All forward consumer banks are installed after a single selected-parameter computation. -/
theorem chirpForwardConsumerSetup_exec (src : TblR 16 → Fin T) (hsrc : Function.Injective src)
    (bs : List (ChirpBankTarget 16 T)) (hinj : ∀ b ∈ bs, Function.Injective b.rg)
    (hsep : ∀ b ∈ bs, ∀ r s, b.rg r ≠ src s)
    (hpair : bs.Pairwise (fun b c => ∀ r s, b.rg r ≠ c.rg s))
    (W e : ℕ) (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 16 A) (p α s t : ℕ) (hp : st.val 0 = p) (hα : st.val 1 = α)
    (hs : st.val 14 = s) (ht : st.val 15 = t) (hzero : st.val 13 = 0)
    (hp0 : 1 ≤ p) (hα0 : 1 ≤ α) (hαp : α ^ 2 ≤ p) (ht0 : 1 ≤ t)
    (hroom : 125 * p < 2 ^ W) (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds src S (tblRho W wl nl st))
    (hblank : ∀ b ∈ bs, ∀ r, S.R (b.rg r) = []) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    ∃ v' S' z n, v'.user = v.user ∧
      n ≤ (((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) + 5) * tblC W e +
        ((2 * e + 2 + (6 * w + 11 * W + 6)) + chirpBankFamilyCost src W w bs) ∧
      Exec body (chirpForwardConsumerSetup src bs) (mk v S) n (mk v' S') ∧
      tblHolds src S' (tblRho W wl (List.replicate w tick) z) ∧
      (∀ b ∈ bs, tblHolds b.rg S'
        (tblRho W (List.replicate W tick) (List.replicate w tick) ⟨fun i => z.val (b.index i), []⟩)) ∧
      (z.val 0 = p ∧ z.val 1 = α ∧ z.val 5 = m ∧ z.val 7 = chirpBlockCount t m ∧
        z.val 8 = l ∧ z.val 9 = Γ ∧ z.val 10 = q ∧ z.val 11 = q + l + Γ + 5 ∧
        z.val 12 = p + l + Γ + 5 ∧ z.val 13 = 0 ∧ z.val 14 = s ∧ z.val 15 = t ∧
        z.acc = st.acc ∧ ∀ i, z.val i < 2 ^ W) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ k, (∀ r, k ≠ src r) → (∀ b ∈ bs, ∀ r, k ≠ b.rg r) → S'.R k = S.R k) := by
  dsimp only
  have hd := tblChirpForwardCallerParameters_do (A := A) (W := W) (e := e)
    st p α s t hp hα hs ht hzero hp0 hα0 hαp ht0 hroom hfit
  obtain ⟨z, hz, hruns⟩ := hd.host (body := body) hsrc wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hframe⟩ := hruns v S hS
  have hzfit : ∀ i, z.val i < 2 ^ W := hz.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpBankEmissionSetup_exec (body := body) src hsrc W wl nl z 11
    (hzfit 11) v₁ S₁ hS₁
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (src .wn) (List.replicate (z.val 11) tick) }
  have hS₂ := chirpBankEmissionSetup_holds src hsrc W wl nl z 11 S₁ hS₁
  have hw : z.val 11 = chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
      chirpForwardRingLog p α + chirpForwardGrowth p + 5 := hz.2.2.2.2.2.2.2.1
  obtain ⟨v₃, R, hu₃, he₃, hbanks, hoff⟩ := chirpBankFamily_exec (body := body) src hsrc
    bs hinj hsep hpair W (z.val 11) wl (List.replicate (z.val 11) tick) hwl (by simp) z hzfit v₂ S₂ hS₂
    (by
      intro b hb r
      simp only [S₂, Function.update_of_ne (hsep b hb r .wn)]
      exact (hframe.2.2.2 _ (fun r' => (hsep b hb r r').symm)).trans (hblank b hb r))
  refine ⟨v₃, { S₂ with R := R }, z, _, hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃), ?_, ?_, hz, hframe.1, hframe.2.1, hframe.2.2.1, ?_⟩
  · rw [hnl, hw] at hn₂
    rw [hw]
    exact Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _)
  · rw [← hw]
    intro r
    rw [show ({ S₂ with R := R } : Stacks T A).R (src r) = S₂.R (src r) from
      hoff _ (fun b hb s => (hsep b hb s r).symm)]
    exact hS₂ r
  · simpa only [hw] using hbanks
  · intro k hks hkb
    rw [show ({ S₂ with R := R } : Stacks T A).R k = S₂.R k from hoff k hkb]
    simp only [S₂, Function.update_of_ne (hks .wn)]
    exact hframe.2.2.2 k (fun r => (hks r).symm)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
