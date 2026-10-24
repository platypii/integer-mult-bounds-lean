module

public import IntegerMultBounds.MathlibTM2.Routing.PlacementOperandFrame

/-! Serialize every physical placement input from padded dimension and payload
words, preserving all generated operands and the arbitrary output suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A t₀ : ℕ} {P U : Type}
noncomputable section

def canonicalPlacementWords (n B : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) :
    Fin (swapT t₀+34) → List (Fin (A+4)) :=
  binaryScheduleInputBank binaryScheduleSlot
    (reservoirExchangeSpecs n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hlarge)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k)
    (fun _ => []) (canonicalScalarWidth n) (canonicalScalarWidth B) B [true] []

theorem canonicalPlacementWords_length (n B : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3)
    (i : Fin (swapT t₀+34)) :
    (canonicalPlacementWords (A := A) n B hlarge k i).length ≤
      canonicalScalarWidth n + canonicalScalarWidth B + 1 := by
  by_cases hi : ∃ role : BinaryScheduleReg t₀ 3, binaryScheduleSlot role = i
  · obtain ⟨role,rfl⟩ := hi
    rw [canonicalPlacementWords,binaryScheduleInputBank_at _ binaryScheduleSlot_injective]
    cases role <;> simp [binaryScheduleInputWords,length_binSyms] <;> omega
  · rw [canonicalPlacementWords,binaryScheduleInputBank,Function.extend_apply' _ _ _ hi]
    simp

def canonicalPlacementGeneratePrice (L Lb n : ℕ) :=
  92*L*L+572*L+529 + binaryResizeBatchCost (fun _ : Fin 9 => L) (fun _ => L)
    (fun _ => canonicalScalarWidth n) (List.finRange 9) + (10*L+13) + (10*Lb+12)

def canonicalPlacementSerializeProgram (rg : Fin 53 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) (k : Fin 3) : Pr P T Q A U :=
  .seq (canonicalPlacementScalarProgram rg k) (placementOperandCopy (t₀ := t₀) rg dst delimiter)

theorem canonicalPlacementScalarBank_outside (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (L n B : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3)
    (dst : Fin T) (hoff : ∀ i, rg i ≠ dst) :
    canonicalPlacementScalarBank R rg L n B hlarge k dst = R dst := by
  have he := canonicalPlacementResizedBank_outside R (rg ∘ canonicalPlacementScalarCore) L n hlarge k dst
    (fun i => hoff _)
  simpa [canonicalPlacementScalarBank,headerScalarBank,canonicalPlacementScalarSlot,
    (hoff 50).symm,(hoff 51).symm,(hoff 52).symm] using he

theorem canonicalPlacementSerialize_exec (body : P → Pr P T Q A U)
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4)) (L Lb n B : ℕ)
    (hn : n < 2^L) (hB : B < 2^Lb) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L) (k : Fin 3)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hpayload : S.R (rg 49) = binSyms Lb B)
    (hblank : ∀ i : Fin 53, i ≠ 0 → i ≠ 9 → i ≠ 49 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ canonicalPlacementGeneratePrice L Lb n +
        ((swapT t₀+34)*(6*(canonicalScalarWidth n+canonicalScalarWidth B+1)+7)+1) ∧
      Exec body (canonicalPlacementSerializeProgram (t₀ := t₀) rg dst delimiter k) (mk v S) m
        (mk v' { S with R := (Function.update (canonicalPlacementScalarBank S.R rg L n B hlarge k)
          dst (placementOperandFrame delimiter rg (canonicalPlacementWords (t₀ := t₀) n B hlarge k) ++ S.R dst)) }) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalPlacementScalar_exec body rg hrg L Lb n B hn hB hlarge hdivisor
    k v S hdimension hpayload hblank
  let C : Stacks T A := { S with R := canonicalPlacementScalarBank S.R rg L n B hlarge k }
  have bank := canonicalPlacementScalarBank_physical (t₀ := t₀) S.R rg hrg L n B hlarge k
    (hblank 43 (by decide) (by decide) (by decide))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := placementOperandCopy_exec body rg hrg dst hoff delimiter
    (canonicalPlacementWords (t₀ := t₀) n B hlarge k) (canonicalScalarWidth n+canonicalScalarWidth B+1)
    (canonicalPlacementWords_length n B hlarge k) v₁ C (fun i => congrFun bank i)
    ((canonicalPlacementScalarBank_copyScratch S.R rg hrg L n B hlarge k 44 (by simp)).trans
      (hblank 44 (by decide) (by decide) (by decide)))
    ((canonicalPlacementScalarBank_copyScratch S.R rg hrg L n B hlarge k 48 (by simp)).trans
      (hblank 48 (by decide) (by decide) (by decide)))
  rw [show C.R dst = S.R dst from canonicalPlacementScalarBank_outside S.R rg L n B hlarge k dst hoff] at he₂
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end
end IntegerMultBounds.MathlibTM2.Routing
