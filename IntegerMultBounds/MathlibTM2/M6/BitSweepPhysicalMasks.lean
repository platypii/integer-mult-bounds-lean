module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepPhysicalCycle
public import IntegerMultBounds.MathlibTM2.M6.BitSweepSelectorCompile

/-! Generate the PR589 gather masks and restore the destination clock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Routing RadixDigits RadixCounterData
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepPhysicalMasks_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 37 ↪ Fin T) (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T)
    (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (hr : ∀ i j, p i ≠ rankPool j) (hc : ∀ i j, p i ≠ coordPool j)
    (rg : BinaryMaskReg ↪ Fin T) (out : Fin T) (maskOff : ∀ i ∈ ([1,2] : List (Fin 37)), ∀ j, p i ≠ rg j)
    (outOff : ∀ i, out ≠ p i) (outMask : ∀ j, out ≠ rg j) (n : Fin 9) (role : Role) :
    ∃ (program : Pr P T Q prime U) (C : ℕ), ∀ (w H : ℕ) (parent : Fin 64 → ZMod (prime^w))
      (units : ∀ i, IsUnit (parent i)) (suffix : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime),
    let M := (prime^w)^128
    let last : Fin M := ⟨M-1,by have := pow_pos (pow_pos prime_prime.pos w) 128; dsimp [M]; omega⟩
    let mat := sweepRankMatrices w parent n role
    0 < w → M < 2^H → (S.R (p 7)).length = M →
    S.R (p 0) = (zeros prime_prime.two_le (w*128)).map digitSymbol →
    (S.R (p 5)).length = w*128 → (S.R (p 10)).length = w → (S.R (p 18)).length = H →
    (S.R (p 21)).length = 128*H →
    S.R (p 22) = matrixWords prime H (mat last true) ++ suffix →
    (∃ t, S.R (p 28) = matrixWords prime H (mat last false) ++ t) →
    S.R (p 35) = binSyms H M → S.R (p 36) = binSyms H (prime^w) →
    S.R (p 20) = binSyms H 0 → S.R (p 33) = binSyms H (1 : ZMod (prime^w)).val →
    S.R (p 34) = binSyms H ((prime^w : ℕ) : ZMod M).val →
    (∀ i ∈ ([1,2,3,4,6,9,11,12,13,14,15,16,17,19,23,25,26,27,30,31,32] : List (Fin 37)), S.R (p i) = []) →
    (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    S.R (p 8) = [] → DescriptorCompileReady rg S.R H M → H ≤ M+1 →
    ∃ (perm : Equiv.Perm (Fin M)) (z : HS T Q prime U) (t : ℕ), (∀ d, perm.symm d = nodeSourceRank w parent units n role d) ∧
      z.user = v.user ∧ t ≤ C*M^3 ∧ Exec body program (mk v S) t
        (mk z {S with R := Function.update S.R out ((permutationMasks perm).flatten.map bitSymbol ++ S.R out)}) := by
  obtain ⟨evaluate,cycle⟩ := sweepPhysicalCycle_exec body p rankPool coordPool disjoint hr hc n role
  obtain ⟨K,bill⟩ := sweepPhysicalRankTime_quadratic sweepBinaryRankCode.depth sweepCoordDepth
  let loop := eachSym (p 7) (p 8) (.seq evaluate (advanceSweepRank prime_prime.two_le (sweepLoopPorts.trans p)))
  let masks : Pr P T Q prime U := .seq (moveR (p 2) (p 1) id)
    (.seq (descriptorCompileProgram rg (p 1) (p 2) out) (bclear (p 1)))
  refine ⟨.seq loop (.seq (moveR (p 8) (p 7) id) masks),9*K+404,?_⟩
  intro w H parent units suffix v S M last mat pos fits ticks counter digitWidth fieldWidth bits clock input chart
    rankWord coordWord zero one radix blank blankRank blankCoord saved ready width
  obtain ⟨perm,correct,_⟩ := nodeToSweep_recordPermutation w parent units n role
  obtain ⟨u,R,k,hu,hk,run,spent,stock,buf,keep⟩ := cycle w H parent units suffix v S pos fits ticks counter
    digitWidth fieldWidth bits clock input chart rankWord coordWord zero one radix blank blankRank blankCoord
  let B := {S with R := R}
  obtain ⟨y,hy,rewind⟩ := moveR_exec body (p 8) (p 7) (by simp) id u B
  let frames := (descriptorSelectorFrames (A := prime) H (List.ofFn perm.symm)).reverse
  let F := {S with R := Function.update S.R (p 2) frames}
  have ordered : (⇑perm.symm) = nodeSourceRank w parent units n role := funext correct
  have buffer : R (p 2) = frames := by simpa only [frames,← ordered] using buf
  have restore : movedR R (p 8) (p 7) id (R (p 8)) = F.R := by
    funext i
    by_cases h₇ : i = p 7
    · subst i; simp [F,movedR,stock,saved,spent]
    by_cases h₈ : i = p 8
    · subst i; simp [F,movedR,saved]
    by_cases h₂ : i = p 2
    · subst i; simp [F,movedR,buffer]
    · simp [F,movedR,h₇,h₈,h₂,keep i h₇ h₈ h₂]
  change Exec _ _ _ (2*(R (p 8)).length+2) (mk y {S with R := movedR R (p 8) (p 7) id (R (p 8))}) at rewind
  rw [restore,stock,saved,List.append_nil,List.length_reverse,ticks] at rewind
  have same i : F.R (rg i) = S.R (rg i) := Function.update_of_ne (maskOff 2 (by decide) i).symm _ _
  obtain ⟨z,l,hz,hl,compile⟩ := compileSweepBuffer_exec body rg (p 2) (p 1) out
    (by simp [List.nodup_cons,Ne.symm (outOff 1),Ne.symm (outOff 2)]) (maskOff 1 (by decide)) (maskOff 2 (by decide)) outMask H fits perm y F
    ⟨(same _).trans ready.width,fun i hi => (same i).trans (ready.blank i hi)⟩
    (by simpa [F] using blank 1 (by decide)) (Function.update_self ..)
  refine ⟨perm,z,k+(2*M+2+l),correct,hz.trans (hy.trans hu),?_,Exec.seq run (Exec.seq rewind ?_)⟩
  · have total := radixSweepSelectorCompile_cost prime_prime.two_le fits width (bill w H n role fits)
    change k ≤ M*(_+_+3)+2 at hk
    change _ + _ ≤ (9*K+400)*M^3 at total
    have positive : 0 < M := pow_pos (pow_pos prime_prime.pos _) _
    have cubic : M ≤ M^3 := Nat.le_self_pow (by decide) _
    have lower : 1 ≤ M^3 := by omega
    change l ≤ M*(descriptorCompileCallCost H M+2)+6*(M*(H+1))+8 at hl
    dsimp only [M] at total hk hl cubic lower ⊢
    simp only [Nat.add_mul] at hk hl total ⊢
    omega
  · simpa only [F,Function.update_of_ne (outOff 2),Function.update_idem,← blank 2 (by decide),
      Function.update_eq_self] using compile

end IntegerMultBounds.MathlibTM2.M6.BitNode
