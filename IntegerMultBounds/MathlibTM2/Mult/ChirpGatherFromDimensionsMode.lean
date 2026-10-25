module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherFromDimensions

/-! # Raw window gathering with a retained group count and advance schedule -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Shared gathering retains the block count and schedule instead of requiring those tapes blank. -/
def ChirpRawReady (shared : Bool) (s t m w : ℕ) (r : ChirpRawReg → Fin T) (S : Stacks T A) : Prop :=
  if shared then
    (S.R (r .count)).length = chirpBlockCount t m ∧
    S.R (r .control) = gatherControls A (chirpAdvancesFrom s t m w 0 (chirpBlockCount t m)) ∧
    (∀ q, q ≠ .raw → q ≠ .dst → q ≠ .count → q ≠ .control → S.R (r q) = [])
  else ∀ q, q ≠ .raw → q ≠ .dst → S.R (r q) = []

def chirpGatherFromDimensionsMode (shared : Bool) (rg : TblR 10 → Fin T) (r : ChirpRawReg → Fin T) : Pr P T Q A U :=
  if shared then chirpRawGatherShared rg r else chirpGatherFromDimensions rg r

def chirpGatherFromDimensionsModeCost (shared : Bool) (W e s t m w : ℕ) : ℕ :=
  if shared then chirpRawGatherWithCost true W e s t m w (chirpBlockCount t m)
  else chirpGatherFromDimensionsCost W e s t m w

theorem chirpGatherFromDimensionsMode_exec (shared : Bool) {rg : TblR 10 → Fin T} {r : ChirpRawReg → Fin T}
    (hrg : Function.Injective rg) (hr : Function.Injective r) (hsep : ∀ q b, rg b ≠ r q)
    {W e : ℕ} (wl nl : List (Fin (A + 4))) (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (st : TblSt 10 A) (s t m w : ℕ)
    (hs : st.val 0 = s) (htval : st.val 1 = t) (hm : st.val 2 = m) (hw : st.val 3 = w)
    (hs0 : 0 < s) (hst : s ≤ t) (ht : 0 < t) (hm0 : 0 < m)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (htm : t + m < 2 ^ W) (hproduct : s * (t + m) < 2 ^ W)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) (hsrc : S.R (r .raw) = cstream A w (chirpLine s u))
    (hclean : ChirpRawReady shared s t m w r S) :
    ∃ v' n, v'.user = v.user ∧ n ≤ chirpGatherFromDimensionsModeCost shared W e s t m w ∧
      Exec body (chirpGatherFromDimensionsMode shared rg r) (mk v S) n
        (mk v' { S with R := (Function.update S.R (r .dst)
          ((List.range (chirpBlockCount t m)).flatMap (fun j => cstream A w (chirpWindow s t m j u)) ++ S.R (r .dst))) }) := by
  cases shared with
  | false =>
      exact chirpGatherFromDimensions_exec (body := body) hrg hr hsep wl nl hwl hnl heW
        st s t m w hs htval hm hw hs0 hst ht hm0 hsize hvolume htm hproduct hzero hfit
        u v S hS hsrc hclean
  | true =>
      rcases hclean with ⟨hcount, hcontrol, hblank⟩
      have hstep (j : ℕ) (hj : j < chirpBlockCount t m) : (j + 1) * m ≤ t + m :=
        (Nat.mul_le_mul_right m (Nat.succ_le_of_lt hj)).trans (chirpBlockCount_mul_le t m)
      exact chirpRawGatherWith_exec (body := body) true hrg hr hsep wl nl hwl hnl heW
        st s t m w (chirpBlockCount t m) hs htval hm hw hs0 hst ht hsize hvolume
        (fun j hj => (hstep j hj).trans_lt htm)
        (fun j hj => (Nat.mul_le_mul_left s (hstep j hj)).trans_lt hproduct)
        ((Nat.mul_le_mul_right w (by omega : m ≤ s + 3 * m + 1)).trans_lt hvolume)
        hzero hfit u (fun j hj => chirpBlock_valid ht hm0 hj) v S hS hsrc hcount hcontrol hblank

/-- The exact repeated setup/release charge avoided by retaining the count and schedule. -/
def chirpGatherRegenerationCost (W e s t m w : ℕ) : ℕ :=
  let M := chirpBlockCount t m
  M * (6 * tblC W e + 11 * W + 24) +
    10 * (chirpCenter s t m M * w) + 17 * tblC W e + 11 * W + 16

theorem chirpGatherFromDimensionsModeCost_split (W e s t m w : ℕ) :
    chirpGatherFromDimensionsModeCost false W e s t m w =
      chirpGatherFromDimensionsModeCost true W e s t m w + chirpGatherRegenerationCost W e s t m w := by
  simp only [chirpGatherFromDimensionsModeCost, Bool.false_eq_true, ite_false, ite_true,
    chirpGatherFromDimensionsCost, chirpRawGatherCost, chirpRawGatherWithCost,
    chirpGatherModeCost, chirpRawSweepCost, chirpGatherRegenerationCost]
  ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
