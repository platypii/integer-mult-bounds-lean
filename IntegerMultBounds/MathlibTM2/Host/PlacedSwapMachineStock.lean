module

public import IntegerMultBounds.MathlibTM2.Host.PlacedSwap
public import IntegerMultBounds.MathlibTM2.Host.SwapMachineStock
public import IntegerMultBounds.MathlibTM2.Host.ForeignFrameWithin
public import IntegerMultBounds.Machine.HoareWithinPlacement

/-! Physical placement retains the selected swap's stock bound, exact
represented endpoint and the existing idle-register frame contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host.PlacedSwapMachineStock
noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)

theorem exec_within {t T Q K : ℕ} {P U : Type}
    (body : P → Pr P T Q (prime+K) U)
    (caller : Tapes t prime) (hd : Fin 5 → Fin t) (pay : Fin t)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t) → Fin T) (hι : Function.Injective ι) (hT : swapT t ≤ T)
    (P₀ G B h d : ℕ) (hs : Fin 5 → List Bool)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ i, Counter.value (hs i) = swapValues P₀ G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hp : 0 < P₀) (hg : 0 < G) (hb : 0 < B)
    (htapes : ∀ i, caller.tape (hd i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (hd i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P₀ (2^h) G (2^d) B) → Bool)
    (ht : caller.tape pay = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head pay = 0) (hcaller : ∀ i, 0 ≤ caller.head i ∧ caller.head i ≤ 1)
    (W : Tapes T (prime+K))
    (ha : Placement.active (swapPlacement ι hι hT) W = SwapMachineStock.encodedInput K caller)
    (hW : ∀ j, 0 ≤ W.head j ∧ W.head j ≤ 1)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hrep : RepT W S.L S.R)
    (depth : ℕ) :
    ∃ v' S',
      RepT (Placement.replace (swapPlacement ι hι hT) W
        (SwapMachineStock.encodedInput K (setTape caller pay
          (BinaryRadixRangePrepareAlphabet.word
            (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))) S'.L S'.R ∧
      v'.user = v.user ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      (∀ j, (S'.L j).length+(S'.R j).length ≤ (S.L j).length+(S.R j).length+
        2*swapCost P₀ G B h d hs) ∧
      (∀ j, (∀ i, ι i ≠ j) → S'.L j = S.L j ∧ (S'.R j = S.R j ∨ S'.R j = padR (S.R j))) ∧
      ∃ n ≤ swapCost P₀ G B h d hs*(T+5)+6,
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+
        T*(2*SwapMachineStock.reserve P₀ G B h d+2)+depth+2*(T+4)) depth
        (foreign (placedSwapMachine K hd pay hi hQ ι hι hT)) (mk v S) n (mk v' S') := by
  let R := SwapMachineStock.reserve P₀ G B h d
  let lo : ℤ := -(R : ℤ)
  let upper : ℤ := (R : ℤ)+1
  have hM := SwapMachineStock.runs_within (K := K) caller hd pay hi hQ P₀ G B h d hs
    hhd hdh hv hc hp hg hb htapes hheads x ht hh hcaller
  have hpM := hM.placed_heads_at (swapPlacement ι hι hT) W ha (by
    intro j
    have h := HeadMargin.weaken (Nat.zero_le R)
      (HeadMargin.centered R (hW ((swapPlacement ι hι hT) (Fin.natAdd (swapT t) j))))
    simpa only [Int.natCast_zero,add_zero,Placement.extra,R] using h)
  obtain ⟨v',S',W',⟨w,hw,rfl⟩,hr,hu,hin,hout,hlen,hframe,n,hn,he⟩ :=
    foreign_exec_frame_within (placedSwapMachine K hd pay hi hQ ι hι hT) body
      (placed_idle_injective _ ι hι _) lo upper hpM v S W rfl hrep depth
  subst w
  have hwidth : (upper+1-lo).toNat = 2*R+2 := HeadMargin.centered_width R
  refine ⟨v',S',hr,hu,hin,hout,hlen,hframe,n,hn,?_⟩
  simpa only [hwidth] using he

end
end IntegerMultBounds.MathlibTM2.Host.PlacedSwapMachineStock
