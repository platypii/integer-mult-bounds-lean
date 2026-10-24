module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryBlockExchange
public import IntegerMultBounds.MathlibTM2.Routing.BlockExchangeChain

/-! A reusable binary-input exchange call: layout facts are separated from the
initial tape invariant, so restored calls compose without execution oracles. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

structure BinaryExchangeCall (t₀ T Q n R B : ℕ) (str tmp : Fin T) where
  hd : Fin 5 → Fin t₀
  pay : Fin t₀
  hhd : Function.Injective hd
  hpay : ∀ k, hd k ≠ pay
  hQ : swapStates hd pay hhd ≤ Q
  bank : Fin (swapT t₀) → Fin T
  hbank : Function.Injective bank
  hT : swapT t₀ ≤ T
  hst : str ≠ tmp
  hstr : ∀ j, bank j ≠ str
  htmp : ∀ j, bank j ≠ tmp
  a : ℕ
  b : ℕ
  w : ℕ
  hab : a + w ≤ b
  hb : b + w ≤ n
  hR : 0 < R
  hB : 0 < B
  rg : ExchangeHeaderReg → Fin T
  hrg : Function.Injective rg
  cfg : Fin 5 → Fin T
  hcfg : cfg = fun k => rg (.base (.header k))
  hbankRaw : ∀ j, bank j ∉ exchangeHeaderPrivate rg
  hstrRaw : str ∉ exchangeHeaderPrivate rg
  htmpRaw : tmp ∉ exchangeHeaderPrivate rg
  work : Fin T
  aux : Fin T
  ctmp : Fin T
  hworkRaw : work ∉ exchangeHeaderPrivate rg
  hauxRaw : aux ∉ exchangeHeaderPrivate rg
  hctmpRaw : ctmp ∉ exchangeHeaderPrivate rg
  hregs : ∀ k, [cfg k, bank (reg (hd k)), work, aux, ctmp].Nodup
  hsources : ∀ k j, cfg k ≠ bank (reg (hd j))
  ex : ExchangeExponentReg → Fin T
  hex : Function.Injective ex
  hcanonical : ∀ r, rg (.base .target) ≠ ex r
  hrowSlot : rg (.base .rowExp) = ex .rowExp
  hgapSlot : rg (.base .gapExp) = ex .gapExp
  hlowerSlot : rg .lowerExp = ex .lowerExp
  hheaderOther : ∀ r, r ≠ .base .rowExp → r ≠ .base .gapExp → r ≠ .lowerExp → r ≠ .base .target →
      rg r ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  hbankSetup : ∀ j, bank j ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  hstrSetup : str ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  htmpSetup : tmp ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  hworkSetup : work ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  hauxSetup : aux ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  hctmpSetup : ctmp ∉ exchangeBinarySetupPrivate ex (rg (.base .target))
  rowBits : List Bool
  Lc : ℕ
  L : ℕ
  hn : n < 2 ^ Lc
  hBin : B < 2 ^ L
  hrow : GrowingCounterData.Canonical rowBits
  hrowNe : rowBits ≠ []
  hrowValue : Counter.value rowBits = R
  ex_str : ∀ r, ex r ≠ str
  rg_str : ∀ r, rg r ≠ str
  work_str : work ≠ str
  aux_str : aux ≠ str
  ctmp_str : ctmp ≠ str

namespace BinaryExchangeCall

variable {t₀ T Q K n R B : ℕ} {str tmp : Fin T} {U F : Type}

structure Ready (c : BinaryExchangeCall t₀ T Q n R B str tmp) (S : Stacks T (prime + K)) : Prop where
  hL : ∀ j, S.L j = []
  htmp0 : S.R tmp = []
  hpay0 : S.R (c.bank (reg c.pay)) = []
  hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (c.bank j) = []
  hhdr0 : ∀ k, S.R (c.bank (reg (c.hd k))) = []
  hrows : S.R (c.rg (.base .rows)) = c.rowBits.map bitSymbol
  hblock : S.R (c.rg (.base .block)) = binSyms c.L B
  hwidth : S.R (c.ex .width) = binSyms c.Lc n
  hlower : S.R (c.ex .lower) = binSyms c.Lc c.a
  hupper : S.R (c.ex .upper) = binSyms c.Lc c.b
  hspan : S.R (c.ex .span) = binSyms c.Lc c.w
  hlower0 : S.R (c.ex .lowerExp) = []
  hrow0 : S.R (c.ex .rowExp) = []
  hgap0 : S.R (c.ex .gapExp) = []
  hexScratch : ∀ i, S.R (c.ex (.scratch i)) = []
  hcanonical0 : S.R (c.rg (.base .target)) = []
  hraw0 : ∀ k, S.R (c.rg (.base (.header k))) = []
  hscratch : ∀ i, S.R (c.rg (.base (.scratch i))) = []
  htriple : S.R (c.rg .triple) = []
  hw : S.R c.work = []
  ha : S.R c.aux = []
  hc0 : S.R c.ctmp = []
  hother : ∀ i, i ≠ c.pay → (∀ k, c.hd k ≠ i) →
      ∀ s ∈ S.R (c.bank (reg i)), s ≠ blank ∧ s.val < prime + 4

noncomputable def program (c : BinaryExchangeCall t₀ T Q n R B str tmp) : Pr F T Q (prime + K) U :=
  .seq (exchangeBinarySetupProgram c.ex (c.rg (.base .target)))
    (.seq (.seq (exchangeHeaderProgram c.rg)
      (.seq (installedBlockExchangeProgram c.cfg c.bank c.hd c.work c.aux c.ctmp
        (swapPass c.hd c.pay c.hhd c.hQ c.bank c.hbank c.hT str tmp)) (metadataClean (exchangeHeaderPrivate c.rg))))
      (metadataClean (exchangeBinarySetupPrivate c.ex (c.rg (.base .target)))))

noncomputable def cost (c : BinaryExchangeCall t₀ T Q n R B str tmp) (S : Stacks T (prime + K)) : ℝ :=
  (3 * (c.Lc * (4 * n + 31) + 2 * n + 26) + 10 * c.Lc + 12 : ℕ) +
    generatedExchangeBound c.bank R B n c.a c.b c.w c.L c.rowBits.length c.Lc S + (2 * n + 2 * c.Lc + 9 : ℕ)

theorem cost_le (c : BinaryExchangeCall t₀ T Q n R B str tmp) (S : Stacks T (prime + K))
    (bankBound : ℕ) (hbank : (∑ j, (S.R (c.bank j)).length) ≤ bankBound) :
    c.cost S ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
        ((max 1 c.w : ℕ) : ℝ) ^ Parameters.tau +
      (generatedExchangeUniformOverhead t₀ T n R B c.L c.rowBits.length c.Lc bankBound +
        (3 * (c.Lc * (4 * n + 31) + 2 * n + 26) + 10 * c.Lc + 12) +
        (2 * n + 2 * c.Lc + 9) : ℕ) := by
  have h := generatedExchangeBound_le c.bank R B n c.a c.b c.w c.L c.rowBits.length c.Lc
    bankBound S c.hab c.hb hbank
  unfold cost
  simp only [Nat.cast_add] at h ⊢
  linarith only [h]

theorem cost_uniform_overhead (c : BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) (L rowLength widthLength bankBound : ℕ)
    (hL : c.L ≤ L) (hr : c.rowBits.length ≤ rowLength) (hw : c.Lc ≤ widthLength)
    (hbank : (∑ j, (S.R (c.bank j)).length) ≤ bankBound) :
    c.cost S ≤
      3 * swapConst * (T + 12 * swapT t₀ + 5 : ℕ) * (R * 2 ^ n * B : ℕ) *
        ((max 1 c.w : ℕ) : ℝ) ^ Parameters.tau +
      (generatedExchangeUniformOverhead t₀ T n R B L rowLength widthLength bankBound +
        (3 * (widthLength * (4 * n + 31) + 2 * n + 26) + 10 * widthLength + 12) +
        (2 * n + 2 * widthLength + 9) : ℕ) := by
  have ho := generatedExchangeUniformOverhead_mono t₀ T n R B hL hr hw (le_refl bankBound)
  have hconvert := Nat.mul_le_mul_right (4 * n + 31) hw
  have hn : generatedExchangeUniformOverhead t₀ T n R B c.L c.rowBits.length c.Lc bankBound +
      (3 * (c.Lc * (4 * n + 31) + 2 * n + 26) + 10 * c.Lc + 12) + (2 * n + 2 * c.Lc + 9) ≤
      generatedExchangeUniformOverhead t₀ T n R B L rowLength widthLength bankBound +
      (3 * (widthLength * (4 * n + 31) + 2 * n + 26) + 10 * widthLength + 12) +
      (2 * n + 2 * widthLength + 9) := by omega
  exact (c.cost_le S bankBound hbank).trans (add_le_add (le_refl _) (Nat.cast_le.mpr hn))

def spec (c : BinaryExchangeCall t₀ T Q n R B str tmp) : BlockExchangeSpec n :=
  ⟨c.a, c.b, c.w, c.hab, c.hb⟩

theorem exec (body : F → Pr F T Q (prime + K) U) (c : BinaryExchangeCall t₀ T Q n R B str tmp)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K)) (h : c.Ready S)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ s ∈ r, s.val < 8) (hsrc : S.R str = l.flatten) :
    ∃ (v' : HS T Q (prime + K) U) (m : ℕ), v'.user = v.user ∧ (m : ℝ) ≤ c.cost S ∧
      Exec body c.program (IntegerMultBounds.MathlibTM2.Host.mk v S) m
        (IntegerMultBounds.MathlibTM2.Host.mk v' { S with R := Function.update S.R str (moveRecs (c.spec.rank R) l).flatten }) := by
  exact binaryBlockExchange_exec body
    c.hd c.pay c.hhd c.hpay c.hQ c.bank c.hbank c.hT str tmp c.hst c.hstr c.htmp n c.a c.b c.w c.hab c.hb c.hR c.hB l hl hlB h8 c.rg c.hrg c.cfg c.hcfg c.hbankRaw c.hstrRaw c.htmpRaw c.work c.aux c.ctmp c.hworkRaw c.hauxRaw c.hctmpRaw c.hregs c.hsources c.ex c.hex c.hcanonical c.hrowSlot c.hgapSlot c.hlowerSlot c.hheaderOther c.hbankSetup c.hstrSetup c.htmpSetup c.hworkSetup c.hauxSetup c.hctmpSetup c.rowBits c.Lc c.L c.hn c.hBin c.hrow c.hrowNe c.hrowValue v S h.hL hsrc h.htmp0 h.hpay0 h.hpriv h.hhdr0 h.hrows h.hblock h.hwidth h.hlower h.hupper h.hspan h.hlower0 h.hrow0 h.hgap0 h.hexScratch h.hcanonical0 h.hraw0 h.hscratch h.htriple h.hw h.ha h.hc0 h.hother

theorem Ready.updateStream (c : BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) (h : c.Ready S) (out : List (Fin (prime + K + 4))) :
    c.Ready { S with R := Function.update S.R str out } := by
  have hb (j : Fin (swapT t₀)) : Function.update S.R str out (c.bank j) = S.R (c.bank j) :=
    Function.update_of_ne (c.hstr j) _ _
  have he (r : ExchangeExponentReg) : Function.update S.R str out (c.ex r) = S.R (c.ex r) :=
    Function.update_of_ne (c.ex_str r) _ _
  have hr (r : ExchangeHeaderReg) : Function.update S.R str out (c.rg r) = S.R (c.rg r) :=
    Function.update_of_ne (c.rg_str r) _ _
  constructor
  · exact h.hL
  · simpa only [Function.update_of_ne c.hst.symm] using h.htmp0
  · simpa only [hb] using h.hpay0
  · simpa only [hb] using h.hpriv
  · simpa only [hb] using h.hhdr0
  · simpa only [hr] using h.hrows
  · simpa only [hr] using h.hblock
  · simpa only [he] using h.hwidth
  · simpa only [he] using h.hlower
  · simpa only [he] using h.hupper
  · simpa only [he] using h.hspan
  · simpa only [he] using h.hlower0
  · simpa only [he] using h.hrow0
  · simpa only [he] using h.hgap0
  · simpa only [he] using h.hexScratch
  · simpa only [hr] using h.hcanonical0
  · simpa only [hr] using h.hraw0
  · simpa only [hr] using h.hscratch
  · simpa only [hr] using h.htriple
  · simpa only [Function.update_of_ne c.work_str] using h.hw
  · simpa only [Function.update_of_ne c.aux_str] using h.ha
  · simpa only [Function.update_of_ne c.ctmp_str] using h.hc0
  · simpa only [hb] using h.hother

theorem cost_updateStream (c : BinaryExchangeCall t₀ T Q n R B str tmp)
    (S : Stacks T (prime + K)) (out : List (Fin (prime + K + 4))) :
    c.cost { S with R := Function.update S.R str out } = c.cost S := by
  simp only [cost, generatedExchangeBound, Function.update_of_ne (c.hstr _)]

end BinaryExchangeCall
end IntegerMultBounds.MathlibTM2.Routing
