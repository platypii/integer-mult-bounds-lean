module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepPhysicalMasks
public import IntegerMultBounds.MathlibTM2.M6.BitSweepInverseMasks

/-! Return a compact PR589 block from sweep rank to node rank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Routing RadixDigits RadixCounterData
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepPhysicalReturn_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 37 ↪ Fin T) (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T)
    (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j)
    (hr : ∀ i j, p i ≠ rankPool j) (hc : ∀ i j, p i ≠ coordPool j)
    (rg : BinaryMaskReg ↪ Fin T) (g : Fin 10 ↪ Fin T) (maskOff : ∀ i ∈ ([1,2] : List (Fin 37)), ∀ j, p i ≠ rg j)
    (outOff : ∀ i, g 0 ≠ p i) (outMask : ∀ j, g 0 ≠ rg j)
    (bank : Fin 8 ↪ Fin T) (shared : bank 6 = g 0) (n : Fin 9) (role : Role) :
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
    ∀ (W : ℕ) (rows : Fin M → List (Fin (prime+4))) (tail unit row : List (Fin (prime+4))),
    unit.length = 1 → row.length = M →
    embStk bank S = transposeStacks (embStk bank S) [] [] [] unit row →
    (∀ i, (rows i).length = W) → S.R (g 2) = (List.ofFn (fun j => rows (nodeSourceRank w parent units n role j))).flatten ++ tail →
    (S.R (g 4)).length = M → (S.R (g 3)).length = W → S.R (g 0) = [] →
    (∀ i : Fin 10, 5 ≤ i.val → S.R (g i) = []) →
    ∃ z t, z.user = v.user ∧ t ≤ C*M^3+M*(M*(16*W+18)+26)+2 ∧
      Exec body program (mk v S) t (mk z {S with
        R := Function.update S.R (g 1)
          ((List.ofFn rows).flatten ++ S.R (g 1))}) := by
  obtain ⟨masks,C,run⟩ := sweepPhysicalMasks_exec body p rankPool coordPool disjoint hr hc rg (g 0)
    maskOff outOff outMask n role
  refine ⟨.seq masks (.seq (embProg bank Empty.elim
    (.seq (.seq (.act (peekR 6)) transposeLoop) (.seq (moveR 0 6 id) (uclear 3))))
    (embProg g Empty.elim sweepGatherProgram)),C+66,?_⟩
  intro w H parent units suffix v S M last mat pos fits ticks counter digitWidth fieldWidth bits clock input chart
    rankWord coordWord zero one radix blank blankRank blankCoord saved ready width W rows tail unit row unitLen rowWidth prepared sizes data count record empty fresh
  obtain ⟨perm,u,k,correct,hu,hk,compile⟩ := run w H parent units suffix v S pos fits ticks counter digitWidth
    fieldWidth bits clock input chart rankWord coordWord zero one radix blank blankRank blankCoord saved ready width
  rw [empty,List.append_nil] at compile
  let B := {S with R := Function.update S.R (g 0) ((permutationMasks perm).flatten.map bitSymbol)}
  have keep (i : Fin 10) (hi : i ≠ 0) : B.R (g i) = S.R (g i) := Function.update_of_ne (g.injective.ne hi) _ _
  have layout : embStk bank B = transposeStacks (embStk bank B) []
      ((permutationMasks perm).flatten.map bitSymbol) [] unit row := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h : i = 6
    · subst i
      change Function.update S.R (g 0) _ (bank 6) = _
      rw [shared,Function.update_self]
      rfl
    · have off : bank i ≠ g 0 := shared ▸ bank.injective.ne h
      change Function.update S.R (g 0) _ (bank i) = _
      rw [Function.update_of_ne off]
      have orig := congrArg (fun F : Stacks 8 prime => F.R i) prepared
      fin_cases i <;> first | contradiction | exact orig
  have positive : 0 < M := pow_pos (pow_pos prime_prime.pos _) _
  obtain ⟨z,l,hz,hl,gather⟩ := sweepInverseGather_exec body bank g shared perm positive
    (fun i => rows (perm.symm i)) (fun i => sizes _) tail unit row unitLen rowWidth u B layout
    (by simpa only [correct] using (keep 2 (by decide)).trans data) (by rwa [keep 4 (by decide)])
    (by rwa [keep 3 (by decide)]) (fun i hi => (keep i (by omega)).trans (fresh i hi))
  refine ⟨z,k+l,hz.trans hu,?_,Exec.seq compile ?_⟩
  · change k ≤ C*M^3 at hk
    change l ≤ 60*M^3+M*(M*(16*W+18)+26)+8 at hl
    have power : 1 ≤ M^3 := Nat.one_le_pow _ _ positive
    rw [Nat.add_mul]
    omega
  · simpa only [Equiv.symm_apply_apply,B,Function.update_idem,← empty,Function.update_eq_self,
      Function.update_of_ne (show g 1 ≠ g 0 by simp)] using gather

end IntegerMultBounds.MathlibTM2.M6.BitNode
