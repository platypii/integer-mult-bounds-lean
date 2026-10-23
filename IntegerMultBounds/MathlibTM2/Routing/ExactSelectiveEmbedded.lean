module

public import IntegerMultBounds.MathlibTM2.Routing.ExactSelective
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! The exact R2 primitive inside a larger common routing bank. Embedding
preserves the exact step count and restores every tape except the shared stream. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

variable {T Q K : ℕ} {P P' U : Type}
/-- Exact repair in a shared bank, independent of the chosen reservoir spacing. -/
theorem exactSelectiveEmbeddedOfGeometry_exec (p : Par) (X rb : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (body : P → Pr P repairT Q (prime + K) U)
    (e : Fin repairT → Fin T) (he : Function.Injective e) (ι : P → P')
    (body' : P' → Pr P' T Q (prime + K) U)
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) (embStk e S).R)
    (hempty : ∀ key, S.R (e (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (e j) = []) (hblank : ∀ j, RepairBlank j → S.R (e j) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (e repairHost.src) = l.flatten) :
    let jobs := repairJobs p X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk e S).R jobs
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost (embStk e S).R jobs +
        repairDensityCoreCost p X rb R B scale { embStk e S with R := installed } +
        metadataCleanCost installed repairTargets ∧
      Exec body' (embProg e ι (repairProgram hQ hA)) (mk v S) steps
        (mk v' { S with R := Function.update S.R (e repairHost.src) (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  obtain ⟨v₁, steps, hu₁, hm, he₁⟩ := exactSelectiveOfGeometry_exec p X rb hG hK hguard scale hscale hn hradix hgap active s body hQ hA
    hR hB hrb hs (embDn e v) (embStk e S) data hempty hL hblank l hl hlen hsrc
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream e he ι body body' hbody (repairProgram hQ hA)
    v S v₁ steps repairHost.src (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten he₁
  exact ⟨v₂, steps, hu₂.trans hu₁, hm, he₂⟩


variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

theorem exactSelectiveEmbedded_exec (body : P → Pr P repairT Q (prime + K) U)
    (e : Fin repairT → Fin T) (he : Function.Injective e) (ι : P → P')
    (body' : P' → Pr P' T Q (prime + K) U)
    (hbody : ∀ f, body' (ι f) = embProg e ι (body f))
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (data : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) (embStk e S).R)
    (hempty : ∀ key, S.R (e (repairSetupTarget key)) = [])
    (hL : ∀ j, S.L (e j) = []) (hblank : ∀ j, RepairBlank j → S.R (e j) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R (e repairHost.src) = l.flatten) :
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled (embStk e S).R jobs
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost (embStk e S).R jobs +
        repairDensityCoreCost p₀ X rb R B scale { embStk e S with R := installed } +
        metadataCleanCost installed repairTargets ∧
      Exec body' (embProg e ι (repairProgram hQ hA)) (mk v S) steps
        (mk v' { S with R := Function.update S.R (e repairHost.src) (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  have hg := routingParameters_guards ρ n m (Nat.clog 2 scale)
  have hp : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hnp : (n : ℝ) ≤ scale := by exact_mod_cast hn
  have hlog : (scale : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 scale := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) scale
  have hx := routingParameters_radices ρ n m (Nat.clog 2 scale) scale hp.le hlog
  exact exactSelectiveEmbeddedOfGeometry_exec p₀ X rb hg.1 hg.2.1 hg.2.2
    scale hp hnp hx.1 hx.2 active s body e he ι body' hbody hQ hA hR hB hrb hs
    v S data hempty hL hblank l hl hlen hsrc

end IntegerMultBounds.MathlibTM2.Routing
