module

public import IntegerMultBounds.MathlibTM2.Routing.ReservoirClassLocalTable
public import IntegerMultBounds.MathlibTM2.Routing.MatchingFixedPlacedRepair
public import IntegerMultBounds.MathlibTM2.Routing.RouterMatchingTable

/-! A complete generated/placed repair whose local source table is produced from
an original physical matching. Both the class and local tables are temporary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ T Q K : ℕ} {P P' P'' P''' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
local notation "N₀" => TP₀ + 36
local notation "str₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))
local notation "str₁" => matchingCoreEmbed TP₀ str₀
local notation "table₁" => matchingExtractSlot TP₀ 5

def originalMatchingPlacedProgram (input : GeneratedPlacedInput t₀ Q K P P' U)
    (producer : Fin 57 → Fin T) (repair : Fin N₀ → Fin T)
    (ι₀ : P' → P'') (ι : P'' → P''') (k : Fin 3) (reverse : Bool) : Pr P''' T Q (prime + K) U :=
  .seq (embProg producer Empty.elim (reservoirClassLocalTableProgram (P := Empty) k))
    (.seq (embProg repair ι (matchingGeneratedPlacedProgram input (matchingCoreEmbed TP₀) ι₀
      (matchingExtractSlot TP₀) (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) reverse))
      (bclear (producer 34)))

theorem originalMatchingPlacedRepair_exec (input : GeneratedPlacedInput t₀ Q K P P' U)
    (producer : Fin 57 → Fin T) (hp : Function.Injective producer)
    (repair : Fin N₀ → Fin T) (hr : Function.Injective repair)
    (hjoin : producer 34 = repair table₁)
    (ι₀ : P' → P'') (coreBody : P'' → Pr P'' N₀ Q (prime + K) U)
    (hcore : ∀ f, coreBody (ι₀ f) = embProg (matchingCoreEmbed TP₀) ι₀ (input.placementBody f))
    (ι : P'' → P''') (body : P''' → Pr P''' T Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg repair ι (coreBody f))
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (hn : n < 2 ^ (input.w.indexBits + input.w.strideBits))
    (hsize : input.p.wy = n - 3 * w)
    (hsource : input.source = fun q => Fin.cast hsize.symm
      (reservoirClassLocalMatching n H hfit w hw k mate hinv (Fin.cast hsize q)))
    (hρ : input.p.ρ < input.p.K) (reverse : Bool)
    (htargets : input.targets = matchingDirectionTargets input.source reverse) (Lc : ℕ)
    (hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc)
    (v : HS T Q (prime + K) U) (S : Stacks T (prime + K))
    (hproducerBank : (embStk producer S).R = reservoirClassLocalBank n H hfit w hw k
      (input.w.indexBits + input.w.strideBits) mate)
    (hrepairBank : (embStk repair S).R = Function.update
      (matchingInitialBank (Function.update input.M.R input.coordinateRegister [])
        input.p input.source input.w.indexBits input.w.strideBits Lc) table₁ [])
    (hleft : ∀ j, S.L (repair (matchingCoreEmbed TP₀ j)) = []) :
    ∃ (v' : HS T Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ (reservoirClassLocalTableCost n w (input.w.indexBits + input.w.strideBits) : ℕ) +
        matchingPlacedRepairPrice input Lc + (2 * ((n - 3 * w) * (2 * (input.w.indexBits + input.w.strideBits) + 2)) + 2 : ℕ) ∧
      Exec body (originalMatchingPlacedProgram input producer repair ι₀ ι k reverse) (mk v S) steps
        (mk v' { S with R := Function.update S.R (repair str₁) (moveRecs input.perm input.l).flatten }) := by
  let L := input.w.indexBits + input.w.strideBits
  let localMate := reservoirClassLocalMatching n H hfit w hw k mate hinv
  let localTable := matchingEntryWords (A := prime + K) L (matchingTableEntries (n - 3 * w) (matchingMateCoordinate localMate))
  let inputTable := matchingEntryWords (A := prime + K) L (matchingTableEntries input.p.wy (matchingMateCoordinate input.source))
  have htable : inputTable = localTable := by
    dsimp only [inputTable, localTable]
    rw [hsource, matchingMateCoordinate_cast hsize, hsize]
  let smallBody : Empty → Pr Empty 57 Q (prime + K) U := Empty.elim
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := reservoirClassLocalTable_exec n H hfit w hw k L smallBody hn mate hinv
    (embDn producer v) (embStk producer S) hproducerBank
  obtain ⟨v₂, hu₂, he₂⟩ := exec_emb_stream producer hp Empty.elim smallBody body
    (by intro f; exact f.elim) (reservoirClassLocalTableProgram k) v S v₁ m₁ 34 localTable he₁
  let G : Stacks T (prime + K) := { S with R := Function.update S.R (producer 34) localTable }
  have hG : G = { S with R := Function.update S.R (repair table₁) inputTable } := by dsimp only [G]; rw [← htable, hjoin]
  have hready : (embStk repair G).R = matchingInitialBank
      (Function.update input.M.R input.coordinateRegister []) input.p input.source input.w.indexBits input.w.strideBits Lc := by
    rw [hG, embStk_update_stream repair hr]
    change Function.update (embStk repair S).R table₁ inputTable = _
    rw [hrepairBank, Function.update_idem]
    have ht : matchingInitialBank (Function.update input.M.R input.coordinateRegister [])
        input.p input.source input.w.indexBits input.w.strideBits Lc table₁ = inputTable := by
      simp [matchingInitialBank, matchingProductionBank_extract, matchingWorkspaceWords, inputTable, L]
    rw [← ht]
    exact Function.update_eq_self _ _
  have hsourceInv : Function.Involutive input.source := by
    rw [hsource]
    intro q
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
    rw [reservoirClassLocalMatching_involutive n H hfit w hw k mate hinv]
    simp only [Fin.cast_cast, Fin.cast_refl, id_eq]
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := matchingFixedPlacedRepair_exec input ι₀ coreBody hcore hρ hsourceInv reverse
    htargets (by rw [hsize]; omega) Lc hcountFit (embDn repair v₂) (embStk repair G) hready hleft
  obtain ⟨v₄, hu₄, he₄⟩ := exec_emb_stream repair hr ι coreBody body hbody
    (matchingGeneratedPlacedProgram input (matchingCoreEmbed TP₀) ι₀ (matchingExtractSlot TP₀)
      (matchingGatherSlot TP₀) (matchingGenerateSlot TP₀) reverse)
    v₂ G v₃ m₃ str₁ (moveRecs input.perm input.l).flatten he₃
  let J : Stacks T (prime + K) := { G with R := Function.update G.R (repair str₁) (moveRecs input.perm input.l).flatten }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec body (producer 34) v₄ J
  have hne : repair str₁ ≠ producer 34 := by
    rw [hjoin]
    exact hr.ne (matchingCoreEmbed_extract TP₀ str₀ 5)
  have hblank : S.R (producer 34) = [] := by
    rw [hjoin]
    have h := congrFun hrepairBank table₁
    simpa only [embStk, Function.comp_apply, Function.update_self] using h
  have hlen : (J.R (producer 34)).length = (n - 3 * w) * (2 * L + 2) := by
    dsimp only [J, G]
    rw [Function.update_of_ne hne.symm, Function.update_self]
    simp only [localTable, matchingEntryWords_length, matchingTableEntries, List.length_map, List.length_range]
  have hfinal : Function.update J.R (producer 34) [] =
      Function.update S.R (repair str₁) (moveRecs input.perm input.l).flatten := by
    funext j
    by_cases hp34 : j = producer 34
    · subst j; simp only [Function.update_self, Function.update_of_ne hne.symm, hblank]
    by_cases hs : j = repair str₁
    · subst j; simp only [J, Function.update_of_ne hp34, Function.update_self]
    · simp only [J, G, Function.update_of_ne hp34, Function.update_of_ne hs]
  rw [hlen, hfinal] at he₅
  refine ⟨v₅, m₁ + (m₃ + (2 * ((n - 3 * w) * (2 * L + 2)) + 2)),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, Exec.seq he₂ (Exec.seq he₄ he₅)⟩
  have hm₁' : (m₁ : ℝ) ≤ (reservoirClassLocalTableCost n w L : ℕ) := by exact_mod_cast hm₁
  dsimp only [L] at hm₁' ⊢
  push_cast
  linarith

end
end IntegerMultBounds.MathlibTM2.Routing
