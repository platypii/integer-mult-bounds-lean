module

public import IntegerMultBounds.MathlibTM2.Routing.ExchangeCost

/-! Closed input-size cost for executed general interval exchanges. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def generatedExchangeBound {t₀ T K : ℕ} (bank : Fin (swapT t₀) → Fin T)
    (R B n a b w L rowLength widthLength : ℕ) (S : Stacks T (prime + K)) : ℝ :=
  (6 * (rowLength + (n - (b + w))) + 6 * (b - a - w) + 52 * L +
    6 * a + 12 * widthLength + 226 : ℕ) +
  (3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
    ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
    (6 * ∑ j, (S.R (bank j)).length +
      14 * ((n - (b + w)) + rowLength + (b - a - w) + 1 + (a + L + 2) + 2 * widthLength) +
      34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 110 : ℕ)) +
  (2 * ((n - (b + w)) + rowLength + (b - a - w) + 1 + (a + L + 2) + 2 * widthLength) + 11 : ℕ)

noncomputable def generatedExchangeUniformOverhead (t₀ T n R B L rowLength widthLength bankBound : ℕ) : ℕ :=
  18 * n + 6 * rowLength + 52 * L + 12 * widthLength + 226 + 6 * bankBound +
    16 * (3 * n + rowLength + L + 2 * widthLength + 3) +
    34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 121

theorem generatedExchangeUniformOverhead_mono (t₀ T n R B : ℕ)
    {L L' rowLength rowLength' widthLength widthLength' bankBound bankBound' : ℕ}
    (hL : L ≤ L') (hr : rowLength ≤ rowLength') (hw : widthLength ≤ widthLength')
    (hb : bankBound ≤ bankBound') :
    generatedExchangeUniformOverhead t₀ T n R B L rowLength widthLength bankBound ≤
      generatedExchangeUniformOverhead t₀ T n R B L' rowLength' widthLength' bankBound' := by
  unfold generatedExchangeUniformOverhead
  gcongr

theorem generatedExchangeBound_le {t₀ T K : ℕ} (bank : Fin (swapT t₀) → Fin T)
    (R B n a b w L rowLength widthLength bankBound : ℕ) (S : Stacks T (prime + K))
    (hab : a + w ≤ b) (hb : b + w ≤ n)
    (hbank : (∑ j, (S.R (bank j)).length) ≤ bankBound) :
    generatedExchangeBound bank R B n a b w L rowLength widthLength S ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
        ((max 1 w : ℕ) : ℝ) ^ Parameters.tau +
      (generatedExchangeUniformOverhead t₀ T n R B L rowLength widthLength bankBound : ℕ) := by
  have ha : a ≤ n := by omega
  have hr : n - (b + w) ≤ n := Nat.sub_le _ _
  have hg : b - a - w ≤ n := by omega
  have hf : (n - (b + w)) + rowLength + (b - a - w) + 1 + (a + L + 2) +
      2 * widthLength ≤ 3 * n + rowLength + L + 2 * widthLength + 3 := by omega
  have hfirst : 6 * (rowLength + (n - (b + w))) + 6 * (b - a - w) + 52 * L +
      6 * a + 12 * widthLength + 226 ≤ 18 * n + 6 * rowLength + 52 * L + 12 * widthLength + 226 := by omega
  have hmiddle : 6 * (∑ j, (S.R (bank j)).length) +
      14 * ((n - (b + w)) + rowLength + (b - a - w) + 1 + (a + L + 2) + 2 * widthLength) +
      34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 110 ≤
      6 * bankBound + 14 * (3 * n + rowLength + L + 2 * widthLength + 3) +
        34 * (R * 2 ^ n * B) + 2 * T + 6 * swapT t₀ + 110 := by omega
  have hlast : 2 * ((n - (b + w)) + rowLength + (b - a - w) + 1 +
      (a + L + 2) + 2 * widthLength) + 11 ≤
      2 * (3 * n + rowLength + L + 2 * widthLength + 3) + 11 := by omega
  have hp := Nat.cast_le (α := ℝ).mpr hfirst
  have hm := Nat.cast_le (α := ℝ).mpr hmiddle
  have hl := Nat.cast_le (α := ℝ).mpr hlast
  unfold generatedExchangeBound generatedExchangeUniformOverhead
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hp hm hl ⊢
  linarith only [hp, hm, hl]

theorem generatedBlockExchange_exec_cost {t₀ T Q K : ℕ} {U F : Type}
    (body : F → Pr F T Q (prime + K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hhd : Function.Injective hd) (hpay : ∀ k, hd k ≠ pay)
    (hQ : swapStates hd pay hhd ≤ Q)
    (bank : Fin (swapT t₀) → Fin T) (hbank : Function.Injective bank) (hT : swapT t₀ ≤ T)
    (str tmp : Fin T) (hst : str ≠ tmp)
    (hstr : ∀ j, bank j ≠ str) (htmp : ∀ j, bank j ≠ tmp)
    (n a b w : ℕ) (hab : a + w ≤ b) (hb : b + w ≤ n)
    {R B : ℕ} (hR : 0 < R) (hB : 0 < B)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8)
    (rg : ExchangeHeaderReg → Fin T) (hrg : Function.Injective rg)
    (cfg : Fin 5 → Fin T) (hcfg : cfg = fun k => rg (.base (.header k)))
    (hbankRaw : ∀ j, bank j ∉ exchangeHeaderPrivate rg)
    (hstrRaw : str ∉ exchangeHeaderPrivate rg) (htmpRaw : tmp ∉ exchangeHeaderPrivate rg)
    (work aux ctmp : Fin T)
    (hworkRaw : work ∉ exchangeHeaderPrivate rg) (hauxRaw : aux ∉ exchangeHeaderPrivate rg)
    (hctmpRaw : ctmp ∉ exchangeHeaderPrivate rg)
    (hregs : ∀ k, [cfg k, bank (reg (hd k)), work, aux, ctmp].Nodup)
    (hsources : ∀ k j, cfg k ≠ bank (reg (hd j)))
    (rowBits widthBits : List Bool) (L : ℕ) (hBin : B < 2 ^ L)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ []) (hrowValue : Counter.value rowBits = R)
    (hwidth : GrowingCounterData.Canonical widthBits) (hwidthValue : Counter.value widthBits = w)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hL : ∀ j, S.L j = []) (hsrc : S.R str = l.flatten) (htmp0 : S.R tmp = [])
    (hpay0 : S.R (bank (reg pay)) = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (bank j) = [])
    (hhdr0 : ∀ k, S.R (bank (reg (hd k))) = [])
    (hrows : S.R (rg (.base .rows)) = rowBits.map bitSymbol)
    (hblock : S.R (rg (.base .block)) = binSyms L B)
    (hwidthInput : S.R (rg (.base .target)) = widthBits.map bitSymbol)
    (hrowExp : (S.R (rg (.base .rowExp))).length = n - (b + w))
    (hgapExp : (S.R (rg (.base .gapExp))).length = b - a - w)
    (hlowerExp : (S.R (rg .lowerExp)).length = a)
    (hraw0 : ∀ k, S.R (rg (.base (.header k))) = [])
    (hscratch : ∀ i, S.R (rg (.base (.scratch i))) = []) (htriple : S.R (rg .triple) = [])
    (hw : S.R work = []) (ha : S.R aux = []) (hc0 : S.R ctmp = [])
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (bank (reg i)), s ≠ blank ∧ s.val < prime + 4) :
    ∃ (payload : List Bool) (v' : HS T Q (prime + K) U) (m : ℕ),
      GrowingCounterData.Canonical payload ∧ Counter.value payload = 2 ^ a * (3 * B) ∧
      payload.length ≤ a + L + 2 ∧ v'.user = v.user ∧
      (m : ℝ) ≤ generatedExchangeBound bank R B n a b w L rowBits.length widthBits.length S ∧
      Exec body (.seq (exchangeHeaderProgram rg)
        (.seq (installedBlockExchangeProgram cfg bank hd work aux ctmp
          (swapPass hd pay hhd hQ bank hbank hT str tmp)) (metadataClean (exchangeHeaderPrivate rg)))) (mk v S) m
        (mk v' { S with R := Function.update S.R str (moveRecs (blockExchangeRank n a b w R hab hb) l).flatten }) := by
  obtain ⟨payload, v', m, hcanonical, hvalue, hlength, hu, hm, he⟩ := generatedBlockExchange_exec body
    hd pay hhd hpay hQ bank hbank hT str tmp hst hstr htmp n a b w hab hb hR hB l hl hlB h8
    rg hrg cfg hcfg hbankRaw hstrRaw htmpRaw work aux ctmp hworkRaw hauxRaw hctmpRaw hregs hsources
    rowBits widthBits L hBin hrow hrowNe hrowValue hwidth hwidthValue v S hL hsrc htmp0 hpay0 hpriv hhdr0
    hrows hblock hwidthInput hrowExp hgapExp hlowerExp hraw0 hscratch htriple hw ha hc0 hother
  have hp := generatedExchangePrice_le bank hbank rg hrg hbankRaw hd hhd R B n w
    (n - (b + w)) (b - a - w) a L S rowBits payload widthBits hlength
  rw [hcfg] at hm
  have hclean : 2 * ((n - (b + w)) + rowBits.length + (b - a - w) + 1 + payload.length + 2 * widthBits.length) + 11 ≤
      2 * ((n - (b + w)) + rowBits.length + (b - a - w) + 1 + (a + L + 2) + 2 * widthBits.length) + 11 := by omega
  have hclean' := (Nat.cast_le (α := ℝ)).mpr hclean
  refine ⟨payload, v', m, hcanonical, hvalue, hlength, hu, ?_, he⟩
  unfold generatedExchangeBound
  linarith only [hm, hp, hclean']

end IntegerMultBounds.MathlibTM2.Routing
