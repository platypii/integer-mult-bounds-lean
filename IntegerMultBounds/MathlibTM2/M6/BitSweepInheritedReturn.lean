module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepInheritedLayout
public import IntegerMultBounds.MathlibTM2.M6.BitSweepHeaderReturn
public import IntegerMultBounds.MathlibTM2.M6.BitSweepBlockScan

/-! Restore every contiguous inherited PR589 block to node order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Stack Host Node Routing CompactRows

theorem sweepInheritedReturn_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
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
    (inv : Fin 8 ↪ Fin T) (maskPort : inv 6 = g 0) (unitPort : inv 4 = p 29) (countPort : inv 7 = p 7)
    (invOff : ∀ i j, i ≠ 4 → i ≠ 7 → inv i ≠ p j)
    (invScan : ∀ i, i ≠ 4 → i ≠ 7 → inv i ≠ s 0 ∧ inv i ≠ s 2)
    (n : Fin 9) (role : Role) :
    ∃ (program : Pr P T Q prime U) (C : ℕ), ∀ (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
      (units : ∀ i, IsUnit (parent i)) (archiveTail : List (Fin (prime+4))),
    let M := prime^(w+1)
    let N := M^128
    let labels := prime^(64*((w+1)*64))
    N < 2^H → H ≤ N+1 → 0 < W → ∀ (x : Fin (M^16*(B*(M^112*W))) → Fin (prime+4)), ∀ (v : HS T Q prime U) (S : Stacks T prime),
    (S.R (p 10)).length = w+1 → (S.R (p 18)).length = H → (S.R (p 29)).length = 1 →
    (S.R (p 37)).length = M.size → S.R (p 38) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ archiveTail →
    (∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,19,20,21,22,23,25,26,27,28,30,31,32,33,34,35,36] : List (Fin 39)), S.R (p i) = []) →
    (∀ j, S.R (pool j) = []) → (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    (∀ j, j ≠ .width → S.R (rg j) = []) → (S.R (g 3)).length = W → S.R (g 0) = [] →
    (∀ i : Fin 10, 5 ≤ i → S.R (g i) = []) → (∀ i : Fin 5, i ≠ 0 → S.R (s i) = []) →
    (∀ i : Fin 8, i ≠ 4 → i ≠ 7 → S.R (inv i) = []) →
    S.R (s 0) = List.ofFn (compactTranspose (x ∘ (nodeToSweep (w+1) B W parent units n role).symm)) →
    ∃ z t, z.user = v.user ∧ t ≤ C*(M^16*(B*labels*(M^112*W)))+4 ∧
      Exec body program (mk v S) t (mk z {S with
      R := Function.update S.R (s 0)
        (List.ofFn (compactTranspose x))}) := by
  obtain ⟨writer,K,write⟩ := sweepHeaderReturn_exec body p pool rankPool coordPool disjoint off hr hc rg g sharedWidth
    maskOff sharedCount gOff outMask inv maskPort unitPort countPort invOff n role
  refine ⟨sweepBlockScan s writer,K+84,?_⟩
  intro w H W B parent units archiveTail M N labels fits width positive x v S exponent bits unit archiveSize
    archive blank poolFree rankFree coordFree maskFree record empty fresh spare invFree data
  let rows (b : Fin B) (i : Fin N) := List.ofFn fun j : Fin W => x (stagedOwnerIndex b (finProdFinEquiv (i,j)))
  have sizes (b i) : (rows b i).length = W := List.length_ofFn
  rw [sweepStagedOutput] at data
  rw [sweepStagedWord]
  let output : Fin B → List (Fin (prime+4)) := fun b => (List.ofFn (rows b)).flatten
  let input := fun b => (List.ofFn fun j => rows b (nodeSourceRank (w+1) parent units n role j)).flatten
  let cost := K*N^3+N*(N*(16*W+18)+26)+2
  have lengths (b) : (input b).length = N*W ∧ (output b).length = N*W := by
    simp [N,M,input,output,List.length_flatten,List.map_ofFn,Function.comp_def,sizes,List.ofFn_const]
  obtain ⟨z,t,hz,ht,run⟩ := sweepBlockScan_exec body s writer (List.finRange B) input output (N*W) cost
    (Nat.mul_pos (pow_pos (pow_pos prime_prime.pos _) _) positive) lengths v S data spare (by
      intro b tail u F source keep
      have bank i := keep (p i) (src ▸ (gOff 2 i (by decide)).symm) (awayP i)
      have gather (i : Fin 10) (hi : i ≠ 2) := keep (g i) (src ▸ g.injective.ne hi) (awayG i)
      obtain ⟨y,k,hy,hk,emit⟩ := write w H W parent units archiveTail fits width (rows b) tail (sizes b) u F
        ⟨(congrArg List.length (bank 10)).trans exponent,(congrArg List.length (bank 18)).trans bits,
          (congrArg List.length (bank 29)).trans unit,(congrArg List.length (bank 37)).trans archiveSize,
          (bank 38).trans archive,fun i hi => (bank i).trans (blank i hi),
          fun j => (keep _ (awayPool j).1 (awayPool j).2).trans (poolFree j),
          fun j => (keep _ (awayRank j).1 (awayRank j).2).trans (rankFree j),
          fun j => (keep _ (awayCoord j).1 (awayCoord j).2).trans (coordFree j),
          fun j hj => (keep _ (awayMask j hj).1 (awayMask j hj).2).trans (maskFree j hj),src ▸ source,
          (congrArg List.length (gather 3 (by decide))).trans record,(gather 0 (by decide)).trans empty,
          fun i hi => (gather i (by omega)).trans (fresh i hi),
          fun i h d => (keep _ (invScan i h d).1 (invScan i h d).2).trans (invFree i h d)⟩
      have buf : F.R (g 1) = [] := (gather 1 (by decide)).trans (dst ▸ spare 1 (by decide))
      rw [buf,List.append_nil,← dst] at emit
      exact ⟨y,k,hy,hk,emit⟩)
  rw [List.length_finRange] at ht
  exact ⟨z,t,hz,ht.trans (sweepBlockScan_volume (w+1) B W K positive),run⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
