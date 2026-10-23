module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBits

/-! The actual canonical residue inputs discharge the repeated scheduler's
stage-data premises. All residues use the same original-matching program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section


def canonicalRouterDelimiter {K : ℕ} : Fin (prime + K + 4) :=
  ⟨8, by
    have h := IntegerMultBounds.Networks.two_pow_le_coefficientBound
      (a := 3) (by
        rw [IntegerMultBounds.Networks.coefficientExponent_eq]
        have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) (by decide : 2 ≤ 2 ^ 16)
        exact (by decide : 3 ≤ 2 ^ 2).trans hpow)
    have hp := IntegerMultBounds.Networks.Shared50ModularControl.coefficientBound_lt_prime
    omega⟩

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen


/-- Execute a concrete list of bulk residues. All stage data, program identities
and metadata admissibility are discharged by the canonical input construction. -/
theorem canonicalRouterBulk_exec (stages : List (Fin (canonicalRouterStride n)))
    (v : HS (originalMatchingScheduleT 6 + 3) Q (prime + K) Unit)
    (S : Stacks (originalMatchingScheduleT 6 + 3) (prime + K))
    (ready : FramedCoreReady (originalMatchingScheduleStream 6) (R * 2 ^ n) B S)
    (hinput : S.R (framedCoreAux (originalMatchingScheduleT 6) 0) = delimitedScheduleInput
      (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
        (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
        k mate canonicalRouterDelimiter) stages)
    (hsaved : S.R (framedCoreAux (originalMatchingScheduleT 6) 2) = []) :
    let r₀ : Fin (canonicalRouterStride n) := ⟨0, by
      have := canonicalRouterGap_pos n
      unfold canonicalRouterStride
      omega⟩
    let program : Pr Empty (originalMatchingScheduleT 6) Q (prime + K) Unit :=
      originalMatchingPlacedProgram (input r₀)
        (originalMatchingProducerEmbed (inactiveClassifierPlacementT 6))
        (originalMatchingRepairEmbed (inactiveClassifierPlacementT 6)) Empty.elim Empty.elim k reverse
    ∃ (v' : HS (originalMatchingScheduleT 6 + 3) Q (prime + K) Unit) (steps : ℕ),
      v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
        (fun r => originalMatchingStepPrice (input r) (canonicalRouterCountWidth n r) n
          (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter) stages +
        (2 * (delimitedScheduleInput (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
          (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter) stages).length + 3 : ℕ) ∧
      Exec (Empty.elim : Empty → Pr Empty (originalMatchingScheduleT 6 + 3) Q (prime + K) Unit)
        (delimitedScheduleProgram (framedCoreAux (originalMatchingScheduleT 6) 0)
          (framedCoreAux (originalMatchingScheduleT 6) 2)
          (framedCoreCallProgram (originalMatchingScheduleStream 6) canonicalRouterDelimiter
            (fun x => decide (x.val < 8)) Empty.elim program)) (mk v S) steps
        (mk v' { S with R := Function.update S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6)) (repairStreamEffect (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B (S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6)))) }) := by
  dsimp only
  obtain ⟨rows, hrows, hshape, hstream⟩ := ready.stream
  have heffect : delimitedScheduleEffect
      (fun r => repairStreamEffect (canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r) B)
      stages (S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6))) = repairStreamEffect (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B (S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6))) := by
    rw [hstream]
    rw [repairStreamEffects_moveRecs _ stages rows hrows (fun row hr => (hshape row hr).1)]
    exact flatten_moveRecs _ rows (fun row hr => (hshape row hr).1)
  rw [← heffect]
  apply framedOriginalMatchingSchedule_exec (inputs := input) (Lc := canonicalRouterCountWidth n)
    (ι₀ := Empty.elim) (coreBody := Empty.elim) (ι := Empty.elim) (body := Empty.elim)
    (hbody := fun f => f.elim) (ιouter := Empty.elim) (outerBody := Empty.elim)
    (houter := fun f => f.elim) (program := _)
    (n := n) (H := routingReservoirWidth n (canonicalRouterGap n))
    (hfit := routingReservoir_fit n (canonicalRouterGap n) hn)
    (w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
    (k := k) (mate := mate) (hinv := hinv) (reverse := reverse)
    (delimiter := canonicalRouterDelimiter) (scan := fun x => decide (x.val < 8)) (stages := stages)
    (hstop := by rfl) (hcore := fun _ _ f => f.elim)
    (hcode := ?_) (data := canonicalRouterStage_data n hn R B hR hB mate hinv k reverse hQ hA l hl hlen)
    (hword := ?_) (v := v) (S := S) ready hinput hsaved
  · intro r hr
    exact canonicalRouterStage_program n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r _
  · intro r hr j hj x hx
    exact decide_eq_true (canonicalRouterStage_words n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j x hx)

end
end IntegerMultBounds.MathlibTM2.Routing
