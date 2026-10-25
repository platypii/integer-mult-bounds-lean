module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankClone
public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardParameterSetup

/-! # Compute forward parameters and install the output dimension bank

The source bank initially holds p, α, a zero word and t. The other source
variables are workspace. All six output inputs and its eight zero workspace
words are installed by the program, rather than assumed initialized.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

namespace ForwardParameters

def caller : Fin 13 → Fin 16 := fun i => ⟨i.val, by omega⟩
theorem caller_inj : Function.Injective caller := by
  intro i j h
  have hv := congrArg (fun x : Fin 16 => x.val) h
  exact Fin.ext hv

def output : Fin 14 → Fin 16 := ![0, 10, 8, 9, 11, 15, 13, 13, 13, 13, 13, 13, 13, 13]

end ForwardParameters

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def chirpForwardOutputBank (src : TblR 16 → Fin T) (dst : TblR 14 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile src (tblChirpForwardParameters.rename ForwardParameters.caller))
    (chirpBankClone src dst ForwardParameters.output)

/-- Execute parameter selection followed by actual installation of a fresh output bank. -/
theorem chirpForwardOutputBank_exec (src : TblR 16 → Fin T) (dst : TblR 14 → Fin T)
    (hsrc : Function.Injective src) (hdst : Function.Injective dst) (hsep : ∀ r s, dst r ≠ src s)
    (W e : ℕ) (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 16 A) (p α t : ℕ) (hp : st.val 0 = p) (hα : st.val 1 = α)
    (hzero : st.val 13 = 0) (ht : st.val 15 = t)
    (hp0 : 1 ≤ p) (hα0 : 1 ≤ α) (hαp : α ^ 2 ≤ p) (hroom : 125 * p < 2 ^ W)
    (hfit : ∀ i, st.val i < 2 ^ W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds src S (tblRho W wl nl st))
    (hblank : ∀ r, S.R (dst r) = []) :
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    ∃ v' S' z n, v'.user = v.user ∧
      n ≤ ((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) * tblC W e +
        chirpBankLoadCost dst (fun i => src (.v (ForwardParameters.output i))) W e (fun _ => W) ∧
      Exec body (chirpForwardOutputBank src dst) (mk v S) n (mk v' S') ∧
      tblHolds src S' (tblRho W wl nl z) ∧
      tblHolds dst S' (tblRho W (List.replicate W tick) (List.replicate e tick)
        ⟨![p, q, l, Γ, w, t, 0, 0, 0, 0, 0, 0, 0, 0], []⟩) ∧
      z.acc = st.acc ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ k, (∀ r, k ≠ src r) → (∀ r, k ≠ dst r) → S'.R k = S.R k) := by
  dsimp only
  have hdo := (tblChirpForwardParameters_do (A := A) (W := W) (e := e)
    (st.restrict ForwardParameters.caller) p α hp hα hp0 hα0 hαp hroom).rename ForwardParameters.caller_inj
  obtain ⟨z, ⟨hz, hzoff⟩, hruns⟩ := hdo.host (body := body) hsrc wl nl hwl hnl heW hfit
  obtain ⟨v₁, S₁, n₁, hu₁, hn₁, he₁, hS₁, hframe⟩ := hruns v S hS
  rcases hz with ⟨hz0, hz1, hz5, hz8, hz9, hz10, hz11, hz12, hacc, hzfit⟩
  change z.val 0 = p at hz0
  change z.val 8 = chirpForwardRingLog p α at hz8
  change z.val 9 = chirpForwardGrowth p at hz9
  change z.val 10 = chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) at hz10
  change z.val 11 = chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) + chirpForwardRingLog p α + chirpForwardGrowth p + 5 at hz11
  have hzfull : ∀ i, z.val i < 2 ^ W := by
    intro i
    by_cases hi : i.val < 13
    · exact hzfit ⟨i.val, hi⟩
    · rw [hzoff i (by intro j h; have hv := congrArg Fin.val h; simp only [ForwardParameters.caller] at hv; omega)]
      exact hfit i
  have h13 : z.val 13 = 0 := (hzoff 13 (by intro i h; have hv := congrArg Fin.val h; simp only [ForwardParameters.caller] at hv; omega)).trans hzero
  have h15 : z.val 15 = t := (hzoff 15 (by intro i h; have hv := congrArg Fin.val h; simp only [ForwardParameters.caller] at hv; omega)).trans ht
  obtain ⟨v₂, R, hu₂, he₂, hout, hoff⟩ := chirpBankClone_exec (body := body) src dst hsrc hdst hsep
    ForwardParameters.output W e wl nl hwl hnl z hzfull v₁ S₁ hS₁
    (fun r => (hframe.2.2.2 _ (fun s => (hsep r s).symm)).trans (hblank r))
  refine ⟨v₂, { S₁ with R := R }, z, _, hu₂.trans hu₁, Nat.add_le_add_right hn₁ _,
    Exec.seq he₁ he₂, ?_, ?_, hacc, hframe.1, hframe.2.1, hframe.2.2.1, ?_⟩
  · intro r
    rw [show ({ S₁ with R := R } : Stacks T A).R (src r) = S₁.R (src r) from
      hoff _ (fun s => (hsep s r).symm)]
    exact hS₁ r
  · have hv : (fun i => z.val (ForwardParameters.output i)) =
        (![p, chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α),
          chirpForwardRingLog p α, chirpForwardGrowth p,
          chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α) +
            chirpForwardRingLog p α + chirpForwardGrowth p + 5, t, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 14 → ℕ) := by
      funext i
      fin_cases i <;> simp [ForwardParameters.output, hz0, hz8, hz9, hz10, hz11, h13, h15]
    simpa only [hv] using hout
  · intro k hks hkd
    exact (hoff k hkd).trans (hframe.2.2.2 k (fun r => (hks r).symm))

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
