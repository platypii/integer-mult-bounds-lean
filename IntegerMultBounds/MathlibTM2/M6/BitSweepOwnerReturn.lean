module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepInheritedReturn
public import IntegerMultBounds.MathlibTM2.M6.BitSweepHostTranspose

/-! Return PR589 records to node order on the owner tape through both compact transposes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Stack Host Node Routing CompactRows

theorem sweepOwnerReturn_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 39 ↪ Fin T) (pool : Fin ((sweepMatrixDepth+1)*13) ↪ Fin T)
    (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T) (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j) (off : ∀ i j, p i ≠ pool j)
    (hr : ∀ i j, p i ≠ rankPool j) (hc : ∀ i j, p i ≠ coordPool j)
    (rg : BinaryMaskReg ↪ Fin T) (g : Fin 10 ↪ Fin T) (sharedWidth : rg .width = p 35)
    (maskOff : ∀ i j, j ≠ .width → p i ≠ rg j) (sharedCount : g 4 = p 7)
    (gOff : ∀ i j, i ≠ 4 → g i ≠ p j) (outMask : ∀ j, g 0 ≠ rg j)
    (s : Fin 5 ↪ Fin T) (src : s 0 = g 2) (dst : s 1 = g 1)
    (awayP : ∀ i, p i ≠ s 2) (awayG : ∀ i, g i ≠ s 2)
    (awayPool : ∀ i, pool i ≠ s 0 ∧ pool i ≠ s 2)
    (awayRank : ∀ i, rankPool i ≠ s 0 ∧ rankPool i ≠ s 2)
    (awayCoord : ∀ i, coordPool i ≠ s 0 ∧ coordPool i ≠ s 2)
    (awayMask : ∀ i, i ≠ .width → rg i ≠ s 0 ∧ rg i ≠ s 2)
    (bank : Fin 8 ↪ Fin T) (dataPort : s 0 = bank 0)
    (bankP : ∀ i j, bank i ≠ p j) (bankPool : ∀ i j, bank i ≠ pool j)
    (bankRank : ∀ i j, bank i ≠ rankPool j) (bankCoord : ∀ i j, bank i ≠ coordPool j)
    (bankMask : ∀ i j, bank i ≠ rg j) (bankG : ∀ i j, j ≠ 2 → bank i ≠ g j)
    (bankS : ∀ i j, j ≠ 0 → bank i ≠ s j)
    (inv : Fin 8 ↪ Fin T) (maskPort : inv 6 = g 0) (unitPort : inv 4 = p 29) (countPort : inv 7 = p 7)
    (invOff : ∀ i j, i ≠ 4 → i ≠ 7 → inv i ≠ p j)
    (invScan : ∀ i, i ≠ 4 → i ≠ 7 → inv i ≠ s 0 ∧ inv i ≠ s 2)
    (bankInv : ∀ j i, i ≠ 4 → i ≠ 7 → bank j ≠ inv i)
    (n : Fin 9) (role : Role) :
    ∃ (program : Pr P T Q prime U) (C : ℕ), ∀ (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
      (units : ∀ i, IsUnit (parent i)) (archiveTail : List (Fin (prime+4))),
    let M := prime^(w+1)
    let N := M^128
    let labels := prime^(64*((w+1)*64))
    N < 2^H → H ≤ N+1 → 0 < W → 0 < B → ∀ (x : Fin (M^16*(B*(M^112*W))) → Fin (prime+4)), ∀ (v : HS T Q prime U) (S : Stacks T prime),
    (S.R (p 10)).length = w+1 → (S.R (p 18)).length = H → (S.R (p 29)).length = 1 →
    (S.R (p 37)).length = M.size → S.R (p 38) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ archiveTail →
    (∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,19,20,21,22,23,25,26,27,28,30,31,32,33,34,35,36] : List (Fin 39)), S.R (p i) = []) →
    (∀ j, S.R (pool j) = []) → (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    (∀ j, j ≠ .width → S.R (rg j) = []) → (S.R (g 3)).length = W → S.R (g 0) = [] →
    (∀ i : Fin 10, 5 ≤ i → S.R (g i) = []) → (∀ i : Fin 5, i ≠ 0 → S.R (s i) = []) →
    (∀ i : Fin 8, i ≠ 4 → i ≠ 7 → S.R (inv i) = []) →
    ∀ (record row : List (Fin (prime+4))), record.length = M^112*W → row.length = B*(M^112*W) →
    embStk bank S = transposeStacks (embStk bank S) [] (List.ofFn (x ∘ (nodeToSweep (w+1) B W parent units n role).symm)) [] record row →
    ∃ z t, z.user = v.user ∧ t ≤ C*(M^16*(B*labels*(M^112*W)))+8 ∧
      Exec body program (mk v S) t (mk z {S with
      R := Function.update S.R (bank 6)
        (List.ofFn x)}) := by
  obtain ⟨middle,C,convert⟩ := sweepInheritedReturn_exec body p pool rankPool coordPool disjoint off hr hc rg g
    sharedWidth maskOff sharedCount gOff outMask s src dst awayP awayG awayPool awayRank awayCoord awayMask
    inv maskPort unitPort countPort invOff invScan n role
  obtain ⟨program,execute⟩ := sweepHostTranspose_exec body bank middle
  refine ⟨program,C+104,?_⟩
  intro w H W B parent units archiveTail M N labels fits width positive blocks x v S exponent bits unit archiveSize
    archive blank poolFree rankFree coordFree maskFree recordWidth empty fresh spare invFree record row length rowLen prepared
  let volume := M^16*(B*labels*(M^112*W))
  obtain ⟨z,t,hz,ht,run⟩ := execute (w+1) B (M^112*W) blocks (Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) positive)
    (x ∘ (nodeToSweep (w+1) B W parent units n role).symm) x record row (C*volume+4) v S length rowLen prepared (by
      intro a F input frame
      have keep i := frame (p i) (fun j => bankP j i)
      obtain ⟨b,l,hb,hl,pass⟩ := convert w H W B parent units archiveTail fits width positive x a F
        ((congrArg List.length (keep 10)).trans exponent) ((congrArg List.length (keep 18)).trans bits)
        ((congrArg List.length (keep 29)).trans unit) ((congrArg List.length (keep 37)).trans archiveSize)
        ((keep 38).trans archive) (fun i hi => (keep i).trans (blank i hi))
        (fun i => (frame _ (fun j => bankPool j i)).trans (poolFree i))
        (fun i => (frame _ (fun j => bankRank j i)).trans (rankFree i))
        (fun i => (frame _ (fun j => bankCoord j i)).trans (coordFree i))
        (fun i hi => (frame _ (fun j => bankMask j i)).trans (maskFree i hi))
        ((congrArg List.length (frame _ (fun j => bankG j 3 (by decide)))).trans recordWidth)
        ((frame _ (fun j => bankG j 0 (by decide))).trans empty)
        (fun i hi => (frame _ (fun j => bankG j i (by omega))).trans (fresh i hi))
        (fun i hi => (frame _ (fun j => bankS j i hi)).trans (spare i hi))
        (fun i h d => (frame _ (fun j => bankInv j i h d)).trans (invFree i h d)) (dataPort ▸ input)
      exact ⟨b,l,hb,hl,by simpa only [dataPort] using pass⟩)
  change t ≤ C*volume+4+104*volume+4 at ht
  exact ⟨z,t,hz,by change t ≤ (C+104)*volume+8; rw [Nat.add_mul]; omega,run⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
