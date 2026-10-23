module

public import IntegerMultBounds.MathlibTM2.Routing.GeneratedPlacedCoordinateInput
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProductionSetup

/-! Actual matching-table production followed by the complete generated/placed
repair and coordinate-input erasure. The supplied coordinate tape starts blank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ T Q K : ℕ} {P P' P'' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))

def matchingGeneratedPlacedProgram (input : GeneratedPlacedInput t₀ Q K P P' U)
    (e : Fin TP₀ → Fin T) (ι : P' → P'') (extract : Fin 8 → Fin T)
    (gather : Fin 18 → Fin T) (generate : Fin 11 → Fin T) (reverse : Bool) : Pr P'' T Q (prime + K) U :=
  .seq (matchingFullProfileProductionProgram extract gather generate reverse (e input.coordinateRegister))
    (.seq (embProg e ι (allSourcePlacedFixedProgram input.keySrc input.raw input.activity input.hQ input.hA
      input.hd input.pay input.hhd input.hQplacement input.hT input.ι)) (bclear (e input.coordinateRegister)))

theorem matchingGeneratedPlacedRepair_exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (e : Fin TP₀ → Fin T) (he : Function.Injective e) (ι : P' → P'')
    (body : P'' → Pr P'' T Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg e ι (input.placementBody f))
    (Lc : ℕ) (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (setup : MatchingProductionSetup input.p input.source input.w.indexBits input.w.strideBits Lc
      (e input.coordinateRegister) S)
    (htargets : input.targets = matchingDirectionTargets input.source setup.reverse)
    (hbank : (embStk e S).R = Function.update input.M.R input.coordinateRegister [])
    (hleft : ∀ j, S.L (e j) = []) :
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (matchingFullProfileProductionCost input.p (input.w.indexBits + input.w.strideBits) input.w.strideBits Lc : ℕ) +
        input.price + (2 * input.coordinateWords.length + 2 : ℕ) ∧
      Exec body (matchingGeneratedPlacedProgram input e ι setup.extract setup.gather setup.generate setup.reverse)
        (mk v S) steps
        (mk v' { S with R := Function.update S.R (e str₀) (moveRecs input.perm input.l).flatten }) := by
  have hcoordinate : S.R (e input.coordinateRegister) = [] := by
    have h := congrFun hbank input.coordinateRegister
    simpa only [embStk, Function.comp_apply, Function.update_self] using h
  have hword : sourceCoordinateInputWords (A := prime + K) input.w.indexBits input.w.strideBits
      (profileCoordinateInputs input.p setup.hK (matchingDirectionTargets input.source setup.reverse) input.source) =
      input.coordinateWords := by
    dsimp only [GeneratedPlacedInput.coordinateWords]
    rw [htargets]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := setup.exec body v
  rw [hword, hcoordinate, List.append_nil] at he₁
  let G : Stacks T (prime + K) := { S with R := Function.update S.R (e input.coordinateRegister) input.coordinateWords }
  have hready : (embStk e G).R = input.M.R := input.installCoordinate_bank e he S hbank
  obtain ⟨u₂, m₂, hu₂, hm₂, he₂⟩ := input.exec_on input.l input.hl input.hlen (embStk e G) hleft
    (by rw [hready, ← input.streamWord, Function.update_eq_self]) (embDn e v₁)
  obtain ⟨v₂, hu₂', he₂'⟩ := exec_emb_stream e he ι input.placementBody body hbody
    (allSourcePlacedFixedProgram input.keySrc input.raw input.activity input.hQ input.hA
      input.hd input.pay input.hhd input.hQplacement input.hT input.ι)
    v₁ G u₂ m₂ str₀ (moveRecs input.perm input.l).flatten he₂
  let H : Stacks T (prime + K) := { G with R := Function.update G.R (e str₀) (moveRecs input.perm input.l).flatten }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (e input.coordinateRegister) v₂ H
  have hne : e input.coordinateRegister ≠ e str₀ := he.ne input.coordinateRegister_ne_stream
  have hlength : (H.R (e input.coordinateRegister)).length = input.coordinateWords.length := by
    dsimp only [H, G]
    rw [Function.update_of_ne hne, Function.update_self]
  have hf : Function.update H.R (e input.coordinateRegister) [] =
      Function.update S.R (e str₀) (moveRecs input.perm input.l).flatten := by
    funext j
    by_cases hc : j = e input.coordinateRegister
    · subst j; simp only [Function.update_self, Function.update_of_ne hne, hcoordinate]
    by_cases hs : j = e str₀
    · subst j; simp only [H, G, Function.update_of_ne hc, Function.update_self]
    · simp only [H, G, Function.update_of_ne hc, Function.update_of_ne hs]
  rw [hlength, hf] at he₃
  refine ⟨v₃, m₁ + (m₂ + (2 * input.coordinateWords.length + 2)),
    hu₃.trans (hu₂'.trans (hu₂.trans hu₁)), ?_, Exec.seq he₁ (Exec.seq he₂' he₃)⟩
  have hm₁' : (m₁ : ℝ) ≤ (matchingFullProfileProductionCost input.p
      (input.w.indexBits + input.w.strideBits) input.w.strideBits Lc : ℕ) := by exact_mod_cast hm₁
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
