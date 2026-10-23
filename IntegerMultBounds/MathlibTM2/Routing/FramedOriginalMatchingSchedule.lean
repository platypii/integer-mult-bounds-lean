module

public import IntegerMultBounds.MathlibTM2.Routing.OriginalMatchingRepairCurrent
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreCall
public import IntegerMultBounds.MathlibTM2.Routing.FramedCoreReady
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankSchedule
public import IntegerMultBounds.MathlibTM2.Routing.RepairScheduleStage

/-! Repeated original-matching repairs use the existing framed loop. All table
production is executed inside each call; stage hypotheses contain no executions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {t₀ Q K M B : ℕ} {I P P' P'' P''' P'''' U : Type}
local notation "TP₀" => inactiveClassifierPlacementT t₀
def originalMatchingScheduleT (t₀ : ℕ) : ℕ := inactiveClassifierPlacementT t₀ + 36 + 57

local notation "N₀" => originalMatchingScheduleT t₀
local notation "rawStr₀" => inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))
def originalMatchingScheduleStream (t₀ : ℕ) : Fin (originalMatchingScheduleT t₀) :=
  originalMatchingRepairEmbed (inactiveClassifierPlacementT t₀)
    (matchingCoreEmbed (inactiveClassifierPlacementT t₀)
      (inactiveClassifierPlacementEmbed (t₀ := t₀) (classifierCore (inactiveConfigurationCore repairHost.src))))

local notation "str₀" => originalMatchingScheduleStream t₀

def originalMatchingFrame (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc n H : ℕ)
    (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (mate : Fin n → Fin n)
    (delimiter : Fin (prime + K + 4)) :=
  delimitedBankFrames delimiter (framedCoreJobs (framedCoreEmbed N₀) str₀
    (originalMatchingPlacedInputBank input Lc n H hfit w hw k mate))

/-- Serialize the actual joined producer/repair bank with a dimension-only word bound. -/
theorem originalMatchingFrame_length_le (input : GeneratedPlacedInput t₀ Q K P P' U)
    (Lc n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (mate : Fin n → Fin n) (delimiter : Fin (prime + K + 4)) (C : ℕ)
    (hcore : ∀ j, j ≠ rawStr₀ → (input.M.R j).length ≤ C) :
    let W := (C + Lc + input.p.wy * (2 * (input.w.indexBits + input.w.strideBits) + 2) +
      input.w.strideBits + input.w.strideBits) +
      (n * (2 * (input.w.indexBits + input.w.strideBits) + 2) +
        12 * (input.w.indexBits + input.w.strideBits) + 12)
    (originalMatchingFrame input Lc n H hfit w hw k mate delimiter).length ≤ N₀ * (W + 1) := by
  dsimp only
  unfold originalMatchingFrame
  apply framedCoreFrames_length_le
  intro j hj
  exact originalMatchingPlacedInputBank_length_le input Lc n H hfit w hw k mate C hcore j hj

def originalMatchingStepPrice (input : GeneratedPlacedInput t₀ Q K P P' U) (Lc n H : ℕ)
    (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3) (mate : Fin n → Fin n)
    (delimiter : Fin (prime + K + 4)) : ℝ :=
  originalMatchingPlacedPrice input Lc n w +
    (6 * (originalMatchingFrame input Lc n H hfit w hw k mate delimiter).length +
      2 * (framedCoreJobs (framedCoreEmbed N₀) str₀
        (originalMatchingPlacedInputBank input Lc n H hfit w hw k mate)).length + 2 : ℕ)

structure OriginalMatchingStageData (input : GeneratedPlacedInput t₀ Q K P P' U)
    (Lc M B n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (reverse : Bool) : Prop where
  count : input.R * 2 ^ fieldsLen (selectiveLen input.p input.X) = M
  width : input.B = B
  hn : n < 2 ^ (input.w.indexBits + input.w.strideBits)
  hsize : input.p.wy = n - 3 * w
  hsource : input.source = fun q => Fin.cast hsize.symm
    (reservoirClassLocalMatching n H hfit w hw k mate hinv (Fin.cast hsize q))
  hρ : input.p.ρ < input.p.K
  htargets : input.targets = matchingDirectionTargets input.source reverse
  hcountFit : (input.p.n * input.p.K) * (2 * (input.w.indexBits + input.w.strideBits) + 2) < 2 ^ Lc

theorem framedOriginalMatchingSchedule_exec
    (inputs : I → GeneratedPlacedInput t₀ Q K P P' U) (Lc : I → ℕ)
    (ι₀ : P' → P'') (coreBody : P'' → Pr P'' (TP₀ + 36) Q (prime + K) U)
    (ι : P'' → P''') (body : P''' → Pr P''' N₀ Q (prime + K) U)
    (hbody : ∀ f, body (ι f) = embProg (originalMatchingRepairEmbed TP₀) ι (coreBody f))
    (ιouter : P''' → P'''') (outerBody : P'''' → Pr P'''' (N₀ + 3) Q (prime + K) U)
    (houter : ∀ f, outerBody (ιouter f) = embProg (framedCoreEmbed N₀) ιouter (body f))
    (program : Pr P''' N₀ Q (prime + K) U)
    (n H : ℕ) (hfit : 9 * H ≤ n) (w : ℕ) (hw : w ≤ H) (k : Fin 3)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (reverse : Bool)
    (delimiter : Fin (prime + K + 4)) (scan : Fin (prime + K + 4) → Bool)
    (hstop : scan delimiter = false) (stages : List I)
    (hcore : ∀ i ∈ stages, ∀ f, coreBody (ι₀ f) = embProg (matchingCoreEmbed TP₀) ι₀ ((inputs i).placementBody f))
    (hcode : ∀ i ∈ stages, originalMatchingPlacedProgram (inputs i) (originalMatchingProducerEmbed TP₀)
      (originalMatchingRepairEmbed TP₀) ι₀ ι k reverse = program)
    (data : ∀ i, OriginalMatchingStageData (inputs i) (Lc i) M B n H hfit w hw k mate hinv reverse)
    (hword : ∀ i ∈ stages, ∀ j, j ≠ str₀ → ∀ x ∈ originalMatchingPlacedInputBank
      (inputs i) (Lc i) n H hfit w hw k mate j, scan x = true)
    (v : HS (N₀ + 3) Q (prime + K) U) (S : Stacks (N₀ + 3) (prime + K))
    (ready : FramedCoreReady str₀ M B S)
    (hinput : S.R (framedCoreAux N₀ 0) = delimitedScheduleInput
      (fun i => originalMatchingFrame (inputs i) (Lc i) n H hfit w hw k mate delimiter) stages)
    (hsaved : S.R (framedCoreAux N₀ 2) = []) :
    ∃ (v' : HS (N₀ + 3) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
        (fun i => originalMatchingStepPrice (inputs i) (Lc i) n H hfit w hw k mate delimiter) stages +
        (2 * (delimitedScheduleInput (fun i => originalMatchingFrame (inputs i) (Lc i) n H hfit w hw k mate delimiter) stages).length + 3 : ℕ) ∧
      Exec outerBody (delimitedScheduleProgram (framedCoreAux N₀ 0) (framedCoreAux N₀ 2)
        (framedCoreCallProgram str₀ delimiter scan ιouter program)) (mk v S) steps
        (mk v' { S with R := Function.update S.R (framedCoreEmbed N₀ str₀) (delimitedScheduleEffect
          (fun i => repairStreamEffect (castRankPerm ((data i).count) (inputs i).perm) B) stages (S.R (framedCoreEmbed N₀ str₀))) }) := by
  apply delimitedSchedule_exec outerBody (framedCoreAux N₀ 0) (framedCoreAux N₀ 2)
    (framedCoreEmbed N₀ str₀) (framedCoreStream_nodup N₀ str₀)
    (fun i => originalMatchingFrame (inputs i) (Lc i) n H hfit w hw k mate delimiter)
    (fun i => repairStreamEffect (castRankPerm ((data i).count) (inputs i).perm) B)
    (fun i => originalMatchingStepPrice (inputs i) (Lc i) n H hfit w hw k mate delimiter)
    (FramedCoreReady str₀ M B) (framedCoreCallProgram str₀ delimiter scan ιouter program)
    stages ?_ ?_ v S ready hinput hsaved
  · intro i _
    unfold originalMatchingFrame
    apply delimitedBankFrames_ne_nil delimiter _ (framedCoreDestinations (framedCoreEmbed N₀) str₀)
      (framedCoreJobs_destinations _ _ _)
    intro he
    have hlen := congrArg List.length he
    simp only [framedCoreDestinations, List.length_map, List.length_nil] at hlen
    exact framedCoreRegisters_ne_nil str₀ (by unfold originalMatchingScheduleT; omega : 2 ≤ N₀) (List.length_eq_zero_iff.mp hlen)
  · intro i hi rest u C hr hsrc
    obtain ⟨l, hl, hrecords, hstream⟩ := hr.stream
    have hcount := hl.trans ((data i).count).symm
    have hshape : ∀ r ∈ l, r.length = (inputs i).B ∧ ∀ a ∈ r, a.val < 8 := by
      simpa only [(data i).width] using hrecords
    let π := castRankPerm ((data i).count) (inputs i).perm
    have hout : (moveRecs (inputs i).perm l).flatten = repairStreamEffect π B (C.R (framedCoreEmbed N₀ str₀)) := by
      rw [repairStreamEffect, hstream, ← flatten_moveRecs π l (fun r hr => (hrecords r hr).1),
        show π = castRankPerm ((data i).count) (inputs i).perm from rfl, moveRecs_castRankPerm]
    have hcall : ∃ (u' : HS (N₀ + 3) Q (prime + K) U) (m : ℕ), u'.user = u.user ∧
        (m : ℝ) ≤ originalMatchingStepPrice (inputs i) (Lc i) n H hfit w hw k mate delimiter ∧
        Exec outerBody (framedCoreCallProgram str₀ delimiter scan ιouter
          (originalMatchingPlacedProgram (inputs i) (originalMatchingProducerEmbed TP₀)
            (originalMatchingRepairEmbed TP₀) ι₀ ι k reverse)) (mk u C) m
          (mk u' { C with R := delimitedCallAdvanced C.R (framedCoreAux N₀ 0) (framedCoreAux N₀ 2) (framedCoreEmbed N₀ str₀) (originalMatchingFrame (inputs i) (Lc i) n H hfit w hw k mate delimiter) rest (moveRecs (inputs i).perm l).flatten }) := by
      apply framedCoreCall_exec body outerBody ιouter houter str₀ delimiter scan hstop
        (originalMatchingPlacedInputBank (inputs i) (Lc i) n H hfit w hw k mate)
        (hword i hi) rest (moveRecs (inputs i).perm l).flatten u C hsrc hr.tmp hr.blank
        (originalMatchingPlacedProgram (inputs i) (originalMatchingProducerEmbed TP₀)
          (originalMatchingRepairEmbed TP₀) ι₀ ι k reverse) (originalMatchingPlacedPrice (inputs i) (Lc i) n w)
      intro u₀
      apply originalMatchingFixedRepair_on (inputs i) l hcount hshape ι₀ coreBody (hcore i hi)
        ι body hbody n H hfit w hw k mate hinv (data i).hn (data i).hsize (data i).hsource
        (data i).hρ reverse (data i).htargets (Lc i) (data i).hcountFit u₀
      · rw [hstream]
        dsimp only [originalMatchingScheduleStream]
        rfl
      · intro j
        exact hr.left (originalMatchingRepairEmbed TP₀ (matchingCoreEmbed TP₀ j))
    obtain ⟨u', m, hu, hm, he⟩ := hcall
    have hc := hcode i hi
    change (originalMatchingPlacedProgram (inputs i) (originalMatchingProducerEmbed TP₀)
      (originalMatchingRepairEmbed TP₀) ι₀ ι k reverse : Pr P''' N₀ Q (prime + K) U) = program at hc
    rw [hc, hout] at he
    exact ⟨u', m, hu, hm, FramedCoreReady.advance str₀ C hr π
      (originalMatchingFrame (inputs i) (Lc i) n H hfit w hw k mate delimiter) rest, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
