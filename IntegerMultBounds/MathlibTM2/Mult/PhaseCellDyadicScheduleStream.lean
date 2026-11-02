module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicScheduleFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposeWiring
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedScheduleData

/-! Identify arithmetic metadata with the streamed worker's canonical plan
inputs. All field-fit obligations follow from the generator's fit gate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem dyadicSelectedRows_wired {T : ℕ} (fuel a b C : ℕ) (h : a+b ≤ fuel)
    (dims : RectangularChunkSwap → Fin 5 → Fin T) :
    (dyadicTransposePlan fuel a b C h).wiredStages dims =
      (dyadicSelectedRows fuel a b C).map (fun row =>
        (⟨dims row.shape,row.outerCount,row.blockWidth,row.fieldBits,row.fieldBits⟩ : BalancedChunkInterchangeStage T)) := by
  rw [DyadicTransposePlan.wiredStages,←dyadicSelectedRows_shape fuel a b C h,List.map_map]
  apply List.map_congr_left
  intro row hr
  simp only [Function.comp_def,DyadicStageRow.shape,Nat.log_pow (by decide : 1 < 2)]

namespace StreamedChunkBank
variable {t₀ T Q K : ℕ}

theorem scheduleStream_eq_flatMap (bank : StreamedChunkBank t₀ T Q) (V : ℕ)
    (rs : List (BalancedChunkInterchangeStage T)) :
    bank.scheduleStream (K := K) V rs = rs.flatMap (fun r =>
      (List.ofFn (swapValues r.outerCount 1 r.blockWidth r.leftBits r.rightBits)).flatMap (binSyms V)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hm : (interchangeDimensionRow bank.dims r.outerCount r.blockWidth r.leftBits r.rightBits).map Prod.fst =
        List.ofFn (swapValues r.outerCount 1 r.blockWidth r.leftBits r.rightBits) := by
      simp only [interchangeDimensionRow,List.map_ofFn,Function.comp_def]
    rw [scheduleStream,List.flatMap_cons,ih,←hm,List.flatMap_map]

theorem canonicalScheduleStream (bank : StreamedChunkBank t₀ T Q) (a b C V : ℕ) :
    bank.scheduleStream (K := K) V
      ((dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => bank.dims)) =
      (dyadicScheduleValues (a+b) a b C).flatMap (binSyms V) := by
  rw [scheduleStream_eq_flatMap,dyadicSelectedRows_wired]
  simp only [dyadicScheduleValues,List.flatMap_map,List.flatMap_assoc,DyadicStageRow.values]

theorem canonicalScheduleFit (bank : StreamedChunkBank t₀ T Q) (a b C V : ℕ)
    (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V) :
    ∀ r ∈ (dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => bank.dims),
      ∀ k, swapValues r.outerCount 1 r.blockWidth r.leftBits r.rightBits k < 2^V := by
  rw [dyadicSelectedRows_wired]
  intro r hr k
  obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hr
  apply dyadicScheduleValues_lt a b C V hbits hfit
  exact List.mem_flatMap.mpr ⟨row,hrow,List.mem_ofFn.mpr ⟨k,rfl⟩⟩

theorem canonicalScheduleLength (bank : StreamedChunkBank t₀ T Q) (a b C : ℕ) :
    ((dyadicTransposePlan (a+b) a b C (by omega)).wiredStages (fun _ => bank.dims)).length =
      dyadicStageCount (a+b) a b := by
  simp only [DyadicTransposePlan.wiredStages,List.length_map,dyadicTransposePlan_stages_length]

end StreamedChunkBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
