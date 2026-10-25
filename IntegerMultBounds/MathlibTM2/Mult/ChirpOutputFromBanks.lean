module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputGenerated
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputFactorFrame

/-! # Execute output arithmetic from binary banks, with no prepared factor or counter tapes -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM

noncomputable def chirpOutputFromBanks {T Q A : ℕ} {P U : Type} (O : ChirpOutputLayout T)
    (dimBank : TblR 14 → Fin T) (factorBank : TblR 48 → Fin T)
    (hT : 64 ≤ T) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (chirpOutputFactorSetup factorBank (O.cr .ys) (O.nr .ys))
    (.seq (chirpOutputGenerated O dimBank hT hQ) (clearWords [O.cr .ys, O.nr .ys]))

def chirpOutputFromBanksCost {T : ℕ} (O : ChirpOutputLayout T) (W N p q l Γ w t m : ℕ) : ℕ :=
  chirpOutputFactorSetupCost W w q Γ m +
    (chirpOutputGeneratedCost O W w N p q l Γ w t + (2 * (m * w + w) + 5))

/-- Factor/counter generation, arithmetic and full cleanup share one actual program. -/
theorem chirpOutputFromBanks_exec {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    (O : ChirpOutputLayout T) (hcross : O.Cross) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (rg : TblR 14 → Fin T) (hrg : Function.Injective rg) (hout : ∀ i r, rg r ≠ O.dim i)
    (hbankOff : ∀ r, rg r ≠ O.cr .ys ∧ rg r ≠ O.nr .ys)
    (trg : TblR 48 → Fin T) (htrg : Function.Injective trg)
    (hEoff : ∀ r, trg r ≠ O.cr .ys) (hNoff : ∀ r, trg r ≠ O.nr .ys)
    {W B w : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = w) (hwW : w ≤ W)
    (st : TblSt 14 A) (factorSt : TblSt 48 A) (s t α p q l Γ m : ℕ)
    (hp : st.val 0 = p) (hq : st.val 1 = q) (hl : st.val 2 = l)
    (hΓ : st.val 3 = Γ) (hw : st.val 4 = w) (ht : st.val 5 = t)
    (hpq : p ≤ q) (hwidth : q + l + Γ + 5 ≤ w)
    (hvolume : t * (p + l + Γ + 5) < 2 ^ W)
    (hzero : ∀ i : Fin 14, 6 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (size : ChirpTableSize W (q - Γ) B)
    (hfq : factorSt.val 19 = q) (hfΓ : factorSt.val 46 = Γ) (hΓq : Γ ≤ q)
    (hfs : factorSt.val 34 = s) (hft : factorSt.val 35 = t) (hfα : factorSt.val 36 = α)
    (hfm : factorSt.val 45 = m) (hf44 : factorSt.val 44 = 0)
    (hqW : q < W) (hαW : 2 * α < 2 ^ W)
    (hs : 0 < s) (hst : s < t) (hα : 0 < α) (hm : 0 < m)
    (hsB : s ≤ B) (htB : t ≤ B) (hαB : α ≤ B) (hmB : m ≤ B)
    (hgate : ∀ b < m, 4 * chirpEN s t b ≤ (q - Γ - 1) * chirpED t α)
    (hrealGate : ∀ b < m, Real.pi * (chirpEN s t b : ℝ) / (chirpED t α : ℝ) ≤ (q - Γ : ℕ) - 1)
    (hgrowth : ∀ b < m, NLogN.chirpE s t (α : ℝ) b ≤ 2 ^ Γ)
    (howned : ∀ i ∈ chirpTableOwned, factorSt.val i = 0)
    (hffit : ∀ i, factorSt.val i < 2 ^ W) (hfacc : factorSt.acc = [])
    (blocks : List (List GaussianInt)) (hlen : ∀ xs ∈ blocks, xs.length = m)
    (htN : t ≤ blocks.flatten.length) (hxs : ∀ c ∈ blocks.flatten, ‖value (q + 1) c‖ ≤ 1)
    (v : HS T Q A U) (S : Stacks T A) (h : ChirpOutputBase O S q w blocks)
    (hbank : tblHolds rg S (tblRho W wl nl st))
    (hfactor : tblHolds trg S (tblRho W wl nl factorSt)) (hblank : ∀ i, S.R (O.bank i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpOutputFromBanksCost O W blocks.flatten.length p q l Γ w t m ∧
      Exec body (chirpOutputFromBanks O rg trg hT hQ) (mk v S) n
        (mk v' { S with R := (Function.update (Function.update S.R (O.cr .xs) []) (O.nr .out)
          (cstream A (p + l + Γ + 5)
            (((chirpOutputNumerators q l Γ blocks (chirpOutputFactors s t α q Γ m)
              (chirpNormalization q α)).take t).map (tdivN (q - p))))) }) := by
  let es := chirpOutputFactors s t α q Γ m
  let a : ℤ := chirpNormalization q α
  let E := cstream A w (es.map fun e => (⟨e, 0⟩ : GaussianInt))
  let N := csyms A w (⟨a, 0⟩ : GaussianInt)
  have hE0 := h.cr_empty .ys (by simp)
  have hN0 := h.nr_empty .ys (by simp)
  have hEN : O.cr .ys ≠ O.nr .ys := O.factor_nr hcross .ys
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := chirpOutputFactorSetup_exec (body := body) htrg
    (O.cr .ys) (O.nr .ys) hEN hEoff hNoff wl nl hwl hnl hwW factorSt size s t α m
    hfq hfΓ hΓq hfs hft hfα hfm hf44 hqW hαW hst.le hsB htB hαB hmB (by omega) hα
    hgate howned hffit hfacc v S hfactor
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R (O.cr .ys) E) (O.nr .ys) N) }
  have he₁' : Exec body (chirpOutputFactorSetup trg (O.cr .ys) (O.nr .ys)) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hE0, hN0, List.append_nil] using he₁
  have off (k : Fin T) (hk : k ≠ O.cr .ys ∧ k ≠ O.nr .ys) : S₁.R k = S.R k := by
    simp only [S₁, Function.update_of_ne hk.1, Function.update_of_ne hk.2]
  have hb₁ : tblHolds rg S₁ (tblRho W wl nl st) := fun r => (off _ (hbankOff r)).trans (hbank r)
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := chirpOutputGenerated_exec (body := body) O hT hQ hA rg hrg hout
    wl nl hwl hnl hwW st p q l Γ w t hp hq hl hΓ hw ht hpq hwidth hvolume hzero hfit
    blocks es a (by simp only [es, chirpOutputFactors_length]; omega)
    (by simpa only [es, chirpOutputFactors_length] using hlen) htN hxs
    (chirpOutputFactors_bound s t α q Γ m hs hst hα hΓq size.precision hrealGate hgrowth)
    (chirpNormalization_abs_le_one q α) v₁ S₁ (h.installFactors hcross es a) hb₁
    (fun i => (off _ ⟨O.bank_cr _ _, O.bank_nr _ _⟩).trans (hblank i))
  let output := cstream A (p + l + Γ + 5)
    (((chirpOutputNumerators q l Γ blocks es a).take t).map (tdivN (q - p)))
  let S₂ : Stacks T A := { S₁ with R :=
    (Function.update (Function.update S₁.R (O.cr .xs) []) (O.nr .out) output) }
  have hE₂ : S₂.R (O.cr .ys) = E := by
    simp only [S₂, S₁, Function.update_of_ne (O.factor_nr hcross .out),
      Function.update_of_ne (O.cr_inj.ne (by decide : CR.ys ≠ .xs)),
      Function.update_of_ne hEN, Function.update_self]
  have hN₂ : S₂.R (O.nr .ys) = N := by
    simp only [S₂, S₁, Function.update_of_ne (O.nr_inj.ne (by decide : CR.ys ≠ .out)),
      Function.update_of_ne (O.input_frame .ys), Function.update_self]
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [O.cr .ys, O.nr .ys] (by simp [hEN]) v₂ S₂
  have hElen : E.length = m * w := by
    dsimp only [E]
    rw [length_cstream, List.length_map]
    exact congrArg (· * w) (chirpOutputFactors_length s t α q Γ m)
  have hNlen : N.length = w := by simp only [N, csyms, Layer.length_coeffSyms]
  have hclear : 2 * ([O.cr .ys, O.nr .ys].map fun k => (S₂.R k).length).sum + 2 * [O.cr .ys, O.nr .ys].length + 1 =
      2 * (m * w + w) + 5 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil, hE₂, hN₂, hElen, hNlen, Nat.add_zero]
  rw [hclear] at he₃
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂ _),
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  exact O.clearFactors hcross S.R E N output hE0 hN0

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
