module

public import IntegerMultBounds.MathlibTM2.Routing.OriginalMatchingFixedRepair
public import IntegerMultBounds.MathlibTM2.Routing.MatchingPlacedFrame

/-! Original-matching calls retain their code, complete price and nonstream bank
while the record stream changes. This is the frame needed for repeated calls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K : ℕ} {P P' P'' P''' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "N₀" => TP₀ + 36 + 57
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))
local notation "str₁" => originalMatchingRepairEmbed TP₀ (matchingCoreEmbed TP₀ str₀)

def originalMatchingPlacedInputBank (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc n H : ℕ)
    (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (mate : Fin n → Fin n) :=
  originalMatchingInputBank TP₀ (matchingPlacedInputBank input Lc)
    (reservoirClassLocalBank n H hfit w hw k (input.w.indexBits + input.w.strideBits) mate)

theorem originalMatchingPlacedInputBank_length_le
    (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc n H : ℕ)
    (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (mate : Fin n → Fin n)
    (C : ℕ) (hcore : ∀ j, j ≠ str₀ → (input.M.R j).length ≤ C)
    (j : Fin N₀) (hj : j ≠ str₁) :
    (originalMatchingPlacedInputBank input Lc n H hfit w hw k mate j).length ≤
      (C + Lc + input.p.wy * (2 * (input.w.indexBits + input.w.strideBits) + 2) +
        input.w.strideBits + input.w.strideBits) +
        (n * (2 * (input.w.indexBits + input.w.strideBits) + 2) +
          12 * (input.w.indexBits + input.w.strideBits) + 12) := by
  apply originalMatchingInputBank_length_le TP₀ _ _ _ _ _ ?_ ?_ j hj
  · intro i hi
    exact matchingPlacedInputBank_length_le input Lc C hcore i hi
  · intro i
    exact reservoirClassLocalBank_length_le n H hfit w hw k _ mate i

def originalMatchingPlacedPrice (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc n w : ℕ) : ℝ :=
  (reservoirClassLocalTableCost n w (input.w.indexBits + input.w.strideBits) : ℕ) +
    matchingPlacedRepairPrice input Lc + (2 * ((n - 3 * w) * (2 * (input.w.indexBits + input.w.strideBits) + 2)) + 2 : ℕ)

variable (input : GeneratedPlacedInput t₀ Q K P P' U)
    (l : List (List (Fin (prime + K + 4))))
    (hl : l.length = input.R * 2 ^ fieldsLen (selectiveLen input.p input.X))
    (hlen : ∀ r ∈ l, r.length = input.B ∧ ∀ a ∈ r, a.val < 8)

theorem GeneratedPlacedInput.replaceRecords_originalMatchingBank (Lc n H : ℕ)
    (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (mate : Fin n → Fin n) :
    originalMatchingPlacedInputBank (input.replaceRecords l hl hlen) Lc n H hfit w hw k mate =
      Function.update (originalMatchingPlacedInputBank input Lc n H hfit w hw k mate) str₁ l.flatten := by
  dsimp only [originalMatchingPlacedInputBank]
  rw [input.replaceRecords_matchingBank l hl hlen]
  exact originalMatchingInputBank_updateRepair _ _ _ _ (matchingCoreEmbed_extract TP₀ str₀ 5) _

theorem GeneratedPlacedInput.replaceRecords_originalMatchingPrice (Lc n w : ℕ) :
    originalMatchingPlacedPrice (input.replaceRecords l hl hlen) Lc n w = originalMatchingPlacedPrice input Lc n w := by
  dsimp only [originalMatchingPlacedPrice]
  rw [input.replaceRecords_matchingPrice l hl hlen]
  rfl

theorem GeneratedPlacedInput.replaceRecords_originalMatchingProgram {T : ℕ}
    (producer : Fin 57 → Fin T) (repair : Fin (TP₀ + 36) → Fin T)
    (ι₀ : P' → P'') (ι : P'' → P''') (k : Fin 3) (reverse : Bool) :
    originalMatchingPlacedProgram (input.replaceRecords l hl hlen) producer repair ι₀ ι k reverse =
      originalMatchingPlacedProgram input producer repair ι₀ ι k reverse := by
  unfold originalMatchingPlacedProgram
  rw [input.replaceRecords_matchingProgram l hl hlen]

include hl hlen in
theorem originalMatchingFixedRepair_on
    (ι₀ : P' → P'') (coreBody : P'' → Pr P'' (TP₀ + 36) Q (prime + K) U)
    (hcore : ∀ f, coreBody (ι₀ f) = embProg (matchingCoreEmbed TP₀) ι₀ (input.placementBody f))
    (ι : P'' → P''') (body : P''' → Pr P''' N₀ Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg (originalMatchingRepairEmbed TP₀) ι (coreBody f))
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hn : n < 2 ^ (input.w.indexBits + input.w.strideBits))
    (hsize : input.p.wy = n - 3 * w)
    (hsource : input.source = fun q => Fin.cast hsize.symm
      (reservoirClassLocalMatching n H hfit w hw k mate hinv (Fin.cast hsize q)))
    (hρ : input.p.ρ < input.p.K) (reverse : Bool)
    (htargets : input.targets = matchingDirectionTargets input.source reverse) (Lc : ℕ)
    (hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc)
    (v : HS N₀ Q (prime + K) U) (S : Stacks N₀ (prime + K))
    (hR : S.R = Function.update (originalMatchingPlacedInputBank input Lc n H hfit w hw k mate) str₁ l.flatten)
    (hleft : ∀ j, S.L (originalMatchingRepairEmbed TP₀ (matchingCoreEmbed TP₀ j)) = []) :
    ∃ (v' : HS N₀ Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ originalMatchingPlacedPrice input Lc n w ∧
      Exec body (originalMatchingPlacedProgram input (originalMatchingProducerEmbed TP₀)
        (originalMatchingRepairEmbed TP₀) ι₀ ι k reverse) (mk v S) steps
        (mk v' { S with R := Function.update S.R str₁ (moveRecs input.perm l).flatten }) := by
  have hbank : S.R = originalMatchingPlacedInputBank (input.replaceRecords l hl hlen) Lc n H hfit w hw k mate := by
    rw [input.replaceRecords_originalMatchingBank l hl hlen]
    exact hR
  obtain ⟨v', steps, hu, hm, he⟩ := originalMatchingFixedRepair_exec (input.replaceRecords l hl hlen)
    ι₀ coreBody hcore ι body hbody n H hfit w hw k mate hinv hn hsize hsource hρ reverse htargets Lc hcountFit v S hbank hleft
  change (steps : ℝ) ≤ originalMatchingPlacedPrice (input.replaceRecords l hl hlen) Lc n w at hm
  rw [input.replaceRecords_originalMatchingPrice l hl hlen] at hm
  rw [input.replaceRecords_originalMatchingProgram l hl hlen] at he
  exact ⟨v', steps, hu, hm, by simpa only [GeneratedPlacedInput.replaceRecords, GeneratedPlacedInput.perm] using he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
