module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementOperandReady
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankTrace

/-! Placement words serialized in physical register order. Unused physical
slots and the caller's record-stream placeholder share a preserved empty word. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A t₀ : ℕ} {P U : Type}
noncomputable section

def placementOperandPhysicalSource : Fin (swapT t₀+34) → Fin 53 :=
  Function.extend binaryScheduleSlot canonicalPlacementOperandSource (fun _ => 43)

theorem canonicalPlacementScalarBank_physical (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (hblank : R (rg 43) = []) :
    let spec := reservoirExchangeSpecs n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hlarge)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k
    (fun i : Fin (swapT t₀+34) => canonicalPlacementScalarBank R rg L n B hlarge k
      (rg (placementOperandPhysicalSource i))) =
      binaryScheduleInputBank binaryScheduleSlot spec (fun _ => [])
        (canonicalScalarWidth n) (canonicalScalarWidth B) B [true] [] := by
  dsimp only
  have bank := canonicalPlacementScalarBank_operands (t₀ := t₀) R rg hrg L n B hlarge k hblank
  funext i
  by_cases hi : ∃ role : BinaryScheduleReg t₀ 3, binaryScheduleSlot role = i
  · obtain ⟨role,rfl⟩ := hi
    rw [placementOperandPhysicalSource,binaryScheduleSlot_injective.extend_apply,
      binaryScheduleInputBank_at _ binaryScheduleSlot_injective]
    exact congrFun bank role
  · rw [placementOperandPhysicalSource,Function.extend_apply' _ _ _ hi,
      binaryScheduleInputBank,Function.extend_apply' _ _ _ hi]
    exact congrFun bank .str

theorem canonicalPlacementScalarBank_copyScratch (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (i : Fin 49)
    (hi : i = 44 ∨ i = 48) :
    canonicalPlacementScalarBank R rg L n B hlarge k (rg (canonicalPlacementScalarCore i)) =
      R (rg (canonicalPlacementScalarCore i)) := by
  rw [canonicalPlacementScalarBank_low R rg hrg L n B hlarge k i]
  apply canonicalPlacementResizedBank_copyReady R (rg ∘ canonicalPlacementScalarCore)
    (hrg.comp canonicalPlacementScalarCore_injective) L n hlarge k i
  rcases hi with rfl | rfl <;> simp

theorem placementOperandPhysicalSource_scratch (i : Fin (swapT t₀+34)) :
    placementOperandPhysicalSource i ≠ 44 ∧ placementOperandPhysicalSource i ≠ 48 := by
  by_cases hi : ∃ role : BinaryScheduleReg t₀ 3, binaryScheduleSlot role = i
  · obtain ⟨role,rfl⟩ := hi
    rw [placementOperandPhysicalSource,binaryScheduleSlot_injective.extend_apply]
    cases role with
    | coordinate stage axis =>
      have h := (placementCoordinateIndex stage axis).isLt
      constructor <;> intro he <;> have hv := congrArg Fin.val he
      all_goals change 34+(placementCoordinateIndex stage axis).val = _ at hv; omega
    | _ => simp [canonicalPlacementOperandSource]
  · rw [placementOperandPhysicalSource,Function.extend_apply' _ _ _ hi]
    decide

def placementOperandFrameJobs (rg : Fin 53 → Fin T)
    (words : Fin (swapT t₀+34) → List (Fin (A+4))) :=
  (List.finRange (swapT t₀+34)).map (fun i => (rg (placementOperandPhysicalSource i),words i))

def placementOperandFrame (delimiter : Fin (A+4)) (rg : Fin 53 → Fin T)
    (words : Fin (swapT t₀+34) → List (Fin (A+4))) :=
  delimitedBankFrames delimiter (placementOperandFrameJobs rg words)

def placementOperandCopy (rg : Fin 53 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 44) (rg 48) delimiter
    ((List.finRange (swapT t₀+34)).map (fun i => rg (placementOperandPhysicalSource i)))

theorem placementOperandCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4))
    (words : Fin (swapT t₀+34) → List (Fin (A+4))) (B : ℕ) (hwords : ∀ i, (words i).length ≤ B)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ i, S.R (rg (placementOperandPhysicalSource i)) = words i)
    (htmp : S.R (rg 44) = []) (hwork : S.R (rg 48) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ (swapT t₀+34)*(6*B+7)+1 ∧
      Exec body (placementOperandCopy (t₀ := t₀) rg dst delimiter) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (placementOperandFrame delimiter rg words ++ S.R dst)) }) := by
  have hreg : [dst,rg 44,rg 48].Nodup := by
    simp [List.nodup_cons,(hoff 44).symm,(hoff 48).symm,hrg.ne (by decide : (44 : Fin 53) ≠ 48)]
  obtain ⟨v',hu,he⟩ := delimitedBankCopy_exec body dst (rg 44) (rg 48) hreg delimiter
    (placementOperandFrameJobs rg words) (by
      intro j hj
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      exact ⟨hoff _,hrg.ne (placementOperandPhysicalSource_scratch i).1,
        hrg.ne (placementOperandPhysicalSource_scratch i).2⟩) v S
    (by intro j hj; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj; exact hbank i) htmp hwork
  have hl : (placementOperandFrameJobs rg words).length = swapT t₀+34 := by
    simp [placementOperandFrameJobs]
  have hf := delimitedBankFrames_length_le delimiter (placementOperandFrameJobs rg words) B (by
    intro j hj
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact hwords i)
  have hc : delimitedBankCopyCost (placementOperandFrameJobs rg words) ≤ (swapT t₀+34)*(6*B+7)+1 := by
    rw [delimitedBankCopyCost_eq delimiter,hl]
    rw [hl] at hf
    nlinarith only [hf]
  refine ⟨v',delimitedBankCopyCost (placementOperandFrameJobs rg words),hu,hc,?_⟩
  simpa only [placementOperandCopy,placementOperandFrame,placementOperandFrameJobs,List.map_map,Function.comp_def] using he

end
end IntegerMultBounds.MathlibTM2.Routing
