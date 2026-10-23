module

public import IntegerMultBounds.MathlibTM2.Routing.RepairProgram
public import IntegerMultBounds.MathlibTM2.Routing.RepairDensity
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveRouter

/-!
# Complete exact selective-update primitive

One fixed finite host program executes metadata installation, complete-rank
keying, the routing schedule, physical classification, exact exceptional repair,
and metadata cleanup. Its destination is the ideal selective XOR on every
address. Explicit logarithmic guards price the sort by the physical density.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

def repairCanonicalHeaders (p : Par) (X rb R B : ℕ) : Fin 2 → Fin 5 → List Bool :=
  routingHeaders p X R (fieldsLen (selectiveKeyLen p X rb) + B)

variable {Q K : ℕ} {P U : Type}
/-- All-address exact execution from raw configuration, with every phase priced,
complete spectators and arbitrary borrowed address fields preserved, and every
host register except the stream restored. -/
theorem exactSelectiveOfGeometry_exec (p : Par) (X rb : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (hguard : p.G + 1 < p.K)
    (scale : ℝ) (hscale : 0 < scale) (hn : (p.n : ℝ) ≤ scale)
    (hradix : 64 * scale ^ 4 ≤ (2 : ℝ) ^ p.G)
    (hgap : 1024 * scale ^ 4 ≤ (2 : ℝ) ^ (p.K - 1 - p.G))
    (active : Fin p.n → Bool) (s : Fin p.n → SlotSource p X)
    (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairT Q (prime + K) U) (S : Stacks repairT (prime + K))
    (data : RepairSetupData p X rb hG hK active s wb wm wp wk R B
      (repairCanonicalHeaders p X rb R B) S.R)
    (hempty : ∀ key, S.R (repairSetupTarget key) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R repairHost.src = l.flatten) :
    let jobs := repairJobs p X rb wb wm wp wk R B
    let installed := metadataInstalled S.R jobs
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost S.R jobs +
        repairDensityCoreCost p X rb R B scale { S with R := installed } +
        metadataCleanCost installed repairTargets ∧
      Exec body (repairProgram hQ hA) (mk v S) steps
        (mk v' { S with R := Function.update S.R repairHost.src (moveRecs (selectiveIdealPerm hK active s R hs) l).flatten }) := by
  obtain ⟨v', steps, hu, hm, he⟩ := repairProgram_exec p X rb hG hK active s hguard
    body hQ hA hR hB hrb hs (repairCanonicalHeaders p X rb R B)
    (fun c j => GrowingCounterData.empty_value _)
    (fun c j => GrowingCounterData.advance_canonical _ [] (Or.inl rfl))
    v S data hempty hL hblank l hl hlen hsrc
  refine ⟨v', steps, hu, ?_, he⟩
  have hc := repairCoreCost_density p X rb R B hguard scale hscale hn hradix hgap
    { S with R := metadataInstalled S.R (repairJobs p X rb wb wm wp wk R B) }
  linarith

variable (ρ n m X rb scale : ℕ) (active : Fin n → Bool)
  (s : Fin n → SlotSource (routingParameters ρ n m (Nat.clog 2 scale)) X)

local notation "p₀" => routingParameters ρ n m (Nat.clog 2 scale)
local notation "hG₀" => And.left (routingParameters_guards ρ n m (Nat.clog 2 scale))
local notation "hK₀" => And.left (And.right (routingParameters_guards ρ n m (Nat.clog 2 scale)))

/-- All-address exact execution from raw configuration, with every phase priced,
complete spectators and arbitrary borrowed address fields preserved, and every
host register except the stream restored. -/
theorem exactSelective_exec (body : P → Pr P repairT Q (prime + K) U)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (hA : 4 ≤ prime + K) (hscale : 0 < scale) (hn : n ≤ scale)
    {wb wm wp wk R B : ℕ} (hR : 0 < R) (hB : 1 ≤ B) (hrb : R ≤ 2 ^ rb)
    (hs : ∀ c, (s c).Allowed active)
    (v : HS repairT Q (prime + K) U) (S : Stacks repairT (prime + K))
    (data : RepairSetupData p₀ X rb hG₀ hK₀ active s wb wm wp wk R B
      (repairCanonicalHeaders p₀ X rb R B) S.R)
    (hempty : ∀ key, S.R (repairSetupTarget key) = [])
    (hL : ∀ j, S.L j = []) (hblank : ∀ j, RepairBlank j → S.R j = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ fieldsLen (selectiveLen p₀ X))
    (hlen : ∀ r ∈ l, r.length = B ∧ ∀ a ∈ r, a.val < 8) (hsrc : S.R repairHost.src = l.flatten) :
    let jobs := repairJobs p₀ X rb wb wm wp wk R B
    let installed := metadataInstalled S.R jobs
    ∃ (v' : HS repairT Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ metadataInstallCost S.R jobs +
        repairDensityCoreCost p₀ X rb R B scale { S with R := installed } +
        metadataCleanCost installed repairTargets ∧
      Exec body (repairProgram hQ hA) (mk v S) steps
        (mk v' { S with R := Function.update S.R repairHost.src (moveRecs (selectiveIdealPerm hK₀ active s R hs) l).flatten }) := by
  have hg := routingParameters_guards ρ n m (Nat.clog 2 scale)
  have hp : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hnp : (n : ℝ) ≤ scale := by exact_mod_cast hn
  have hlog : (scale : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 scale := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) scale
  have hx := routingParameters_radices ρ n m (Nat.clog 2 scale) scale hp.le hlog
  exact exactSelectiveOfGeometry_exec p₀ X rb hg.1 hg.2.1 hg.2.2
    scale hp hnp hx.1 hx.2 active s body hQ hA hR hB hrb hs
    v S data hempty hL hblank l hl hlen hsrc

end IntegerMultBounds.MathlibTM2.Routing
