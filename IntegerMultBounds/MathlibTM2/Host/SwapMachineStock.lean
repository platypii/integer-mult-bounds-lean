module

public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap
public import IntegerMultBounds.MathlibTM2.Host.ForeignWithin
public import IntegerMultBounds.MathlibTM2.Host.LiftWithin
public import IntegerMultBounds.Machine.AlphabetWithin
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryInterchangeRunWithin

/-! The selected binary interchange's actual alphabet/state-adapted foreign
call has a stock trace. Original metadata, caller heads and initial
representation supply the premises; no intermediate execution or stock
certificate is assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host.SwapMachineStock
noncomputable section
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
open IntegerMultBounds.MathlibTM2.M8.Machine

/-- The original tape bank encoded in the host alphabet. -/
def encodedInput {t : ℕ} (K : ℕ) (caller : Tapes t prime) :=
  Alphabet.mapTapes (Alphabet.widen prime K) (BinaryInterchangeRun.input caller)

def reserve (P G B h d : ℕ) : ℕ := BinaryInterchangeRunWithin.coefficient*
  BinaryAdjacentWidthInterchange.volume P (2^h) G (2^d) B

theorem runs_within {t Q K : ℕ}
    (caller : Tapes t prime) (hd : Fin 5 → Fin t) (pay : Fin t)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
    (P₀ G B h d : ℕ) (hs : Fin 5 → List Bool)
    (hhd : h ≤ d+1) (hdh : d ≤ h+1)
    (hv : ∀ i, Counter.value (hs i) = swapValues P₀ G B h d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hp : 0 < P₀) (hg : 0 < G) (hb : 0 < B)
    (htapes : ∀ i, caller.tape (hd i) = RadixZeroFill.encodedBinary (hs i))
    (hheads : ∀ i, caller.head (hd i) = 1)
    (x : Fin (BinaryAdjacentWidthInterchange.volume P₀ (2^h) G (2^d) B) → Bool)
    (ht : caller.tape pay = BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (x i)))
    (hh : caller.head pay = 0) (hcaller : ∀ i, 0 ≤ caller.head i ∧ caller.head i ≤ 1) :
    HoareWithin (liftQ (swapMachine K hd pay hi) hQ) (· = encodedInput K caller)
      (· = encodedInput K (setTape caller pay
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0))
      (swapCost P₀ G B h d hs)
      (fun z => ∀ j, -(reserve P₀ G B h d : ℤ) ≤ z.head j ∧
        z.head j ≤ (reserve P₀ G B h d : ℤ)+1) := by
  let reserve := BinaryInterchangeRunWithin.coefficient*
    BinaryAdjacentWidthInterchange.volume P₀ (2^h) G (2^d) B
  let lo : ℤ := -(reserve : ℤ)
  let upper : ℤ := (reserve : ℤ)+1
  have hbank : ∀ j, 0 ≤ (BinaryInterchangeRun.input caller).head j ∧
      (BinaryInterchangeRun.input caller).head j ≤ 1 := by
    intro j
    rw [(input_ext caller j).1]
    split_ifs with hj
    · exact hcaller _
    · exact ⟨le_refl 0,by decide⟩
  have hm : ∀ j, lo+(reserve : ℕ) ≤ (BinaryInterchangeRun.input caller).head j ∧
      (BinaryInterchangeRun.input caller).head j+(reserve : ℕ) ≤ upper := by
    intro j
    exact HeadMargin.centered reserve (hbank j)
  have hr := BinaryInterchangeRunWithin.runs caller hd pay hi P₀ G B h d hs
    hhd hdh hv hc hp hg hb htapes hheads x ht hh lo upper hm
  have hM := HoareWithin.liftQ hQ lo upper (Alphabet.map_within (Alphabet.widen prime K) lo upper hr)
  apply hM.consequence ?_ ?_ le_rfl (fun _ h => h)
  · intro z hz
    exact ⟨BinaryInterchangeRun.input caller,rfl,hz⟩
  · rintro z ⟨w,rfl,hz⟩
    exact hz

theorem exec_within {t Q K : ℕ} {P U : Type}
    (body : P → Pr P (swapT t) Q (prime+K) U)
    (caller : Tapes t prime) (hd : Fin 5 → Fin t) (pay : Fin t)
    (hi : Function.Injective hd) (hQ : swapStates hd pay hi ≤ Q)
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
    (v : HS (swapT t) Q (prime+K) U) (S : Stacks (swapT t) (prime+K))
    (hrep : RepT (encodedInput K caller) S.L S.R)
    (depth : ℕ) :
    ∃ v' S', RepT (encodedInput K (setTape caller pay
        (BinaryRadixRangePrepareAlphabet.word
          (BinaryAdjacentWidthInterchange.transpose (fun i => bitSymbol (x i)))) 0)) S'.L S'.R ∧
      v'.user = v.user ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      ∃ n ≤ swapCost P₀ G B h d hs*(swapT t+5)+6,
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+
        swapT t*(2*(BinaryInterchangeRunWithin.coefficient*
          BinaryAdjacentWidthInterchange.volume P₀ (2^h) G (2^d) B)+2)+depth+2*(swapT t+4)) depth
        (foreign (liftQ (swapMachine K hd pay hi) hQ)) (mk v S) n (mk v' S') := by
  let R := reserve P₀ G B h d
  let lo : ℤ := -(R : ℤ)
  let upper : ℤ := (R : ℤ)+1
  have hM := runs_within (K := K) caller hd pay hi hQ P₀ G B h d hs hhd hdh hv hc hp hg hb
    htapes hheads x ht hh hcaller
  obtain ⟨v',S',w',hw,hrep',hu,hin,hout,n,hn,he⟩ :=
    foreign_exec_within_hoare_heads (liftQ (swapMachine K hd pay hi) hQ) body lo upper hM
      v S (encodedInput K caller) rfl hrep depth
  subst w'
  have hwidth : (upper+1-lo).toNat = 2*R+2 := HeadMargin.centered_width R
  refine ⟨v',S',hrep',hu,hin,hout,n,hn,?_⟩
  simpa only [hwidth,R,reserve] using he

end
end IntegerMultBounds.MathlibTM2.Host.SwapMachineStock
