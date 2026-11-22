module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepOwnerPermutation
public import IntegerMultBounds.MathlibTM2.M6.BitSweepOwnerSchedule

/-! Run the stage address permutation on every role using a shared transpose workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Stack Host Node Routing CompactRows

private theorem finiteCostBound {ι : Type} [Fintype ι] (cost : ι → ℕ) :
    ∃ C : ℕ, ∀ i, cost i ≤ C :=
  ⟨Finset.univ.sup cost,fun i => Finset.le_sup (f := cost) (Finset.mem_univ i)⟩

theorem sweepAllOwners_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
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
    (owners : Fin 142081 ↪ Fin T) (bank : Role → Fin 8 ↪ Fin T) (dataPort : ∀ r, s 0 = bank r 0)
    (ownerPort : ∀ r, bank r 6 = owners (sweepRoleTape r))
    (shared : ∀ r a i, i ≠ 6 → bank r i = bank a i)
    (bankP : ∀ r i j, bank r i ≠ p j) (bankPool : ∀ r i j, bank r i ≠ pool j)
    (bankRank : ∀ r i j, bank r i ≠ rankPool j) (bankCoord : ∀ r i j, bank r i ≠ coordPool j)
    (bankMask : ∀ r i j, bank r i ≠ rg j) (bankG : ∀ r i j, j ≠ 2 → bank r i ≠ g j)
    (bankS : ∀ r i j, j ≠ 0 → bank r i ≠ s j)
    (n : Fin 9) :
    ∃ (program : Pr P T Q prime U) (C : ℕ), ∀ (w H W B : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
      (units : ∀ i, IsUnit (parent i)) (archiveTail : List (Fin (prime+4))),
    let M := prime^(w+1)
    let N := M^128
    let labels := prime^(64*((w+1)*64))
    N < 2^H → H ≤ N+1 → 0 < W → 0 < B → ∀ (x : Role → Fin (M^16*(B*(M^112*W))) → Fin (prime+4)), ∀ (v : HS T Q prime U) (S : Stacks T prime),
    (S.R (p 10)).length = w+1 → (S.R (p 18)).length = H → (S.R (p 29)).length = 1 →
    (S.R (p 37)).length = M.size → S.R (p 38) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ archiveTail →
    (∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,19,20,21,22,23,25,26,27,28,30,31,32,33,34,35,36] : List (Fin 39)), S.R (p i) = []) →
    (∀ j, S.R (pool j) = []) → (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    (∀ j, j ≠ .width → S.R (rg j) = []) → (S.R (g 3)).length = W → S.R (g 0) = [] →
    (∀ i : Fin 10, 5 ≤ i → S.R (g i) = []) → (∀ i : Fin 5, i ≠ 0 → S.R (s i) = []) →
    ∀ (record row : List (Fin (prime+4))), record.length = M^112*W → row.length = B*(M^112*W) →
    (∀ r, embStk (bank r) S = transposeStacks (embStk (bank r) S) [] (List.ofFn (x r)) [] record row) →
    ∃ z R t, z.user = v.user ∧ t ≤ 142080*(C*(M^16*(B*labels*(M^112*W)))+8)+1 ∧
      Exec body program (mk v S) t (mk z {S with R := R}) ∧
      (∀ r, R (owners (sweepRoleTape r)) = List.ofFn (x r ∘ (nodeToSweep (w+1) B W parent units n r).symm)) ∧
      ∀ j, (∀ r, owners (sweepRoleTape r) ≠ j) → R j = S.R j := by
  classical
  choose code coeff run using fun r => sweepOwnerPermutation_exec body p pool rankPool coordPool disjoint off hr hc rg g
    sharedWidth maskOff sharedCount gOff outMask s src dst awayP awayG awayPool awayRank awayCoord awayMask
    (bank r) (dataPort r) (bankP r) (bankPool r) (bankRank r) (bankCoord r) (bankMask r) (bankG r) (bankS r) n r
  obtain ⟨C,bound⟩ := finiteCostBound coeff
  obtain ⟨program,execute⟩ := sweepOwnerSchedule_exec body owners code
  refine ⟨program,C,?_⟩
  intro w H W B parent units archiveTail M N labels fits width positive blocks x v S exponent bits unit archiveSize
    archive blank poolFree rankFree coordFree maskFree recordWidth empty fresh spare record row len rowLen prepared
  let volume := M^16*(B*labels*(M^112*W))
  apply execute (fun r => List.ofFn (x r)) (fun r => List.ofFn (x r ∘ (nodeToSweep (w+1) B W parent units n r).symm)) C volume
  · intro r
    rw [show (sweepRoleTape.trans owners) r = bank r 6 from (ownerPort r).symm]
    exact congrArg (fun E : Stacks 8 prime => E.R 6) (prepared r)
  · intro r a F input keep
    have preserved (j) (h : ∀ b, bank b 6 ≠ j) : F.R j = S.R j :=
      keep j (fun b => (ownerPort b) ▸ h b)
    have slot i := preserved _ (fun b => bankP b 6 i)
    have transposeReady : embStk (bank r) F =
        transposeStacks (embStk (bank r) F) [] (List.ofFn (x r)) [] record row := by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = 6
      · subst i; change F.R (bank r 6) = List.ofFn (x r); rwa [ownerPort]
      · have unchanged := preserved (bank r i) (fun b => by rw [shared r b i hi]; exact (bank b).injective.ne (Ne.symm hi))
        exact unchanged.trans (congrArg (fun E : Stacks 8 prime => E.R i) (prepared r))
    obtain ⟨y,l,hy,hl,pass⟩ := run r w H W B parent units archiveTail fits width positive blocks (x r) a F
      ((congrArg List.length (slot 10)).trans exponent) ((congrArg List.length (slot 18)).trans bits)
      ((congrArg List.length (slot 29)).trans unit) ((congrArg List.length (slot 37)).trans archiveSize)
      ((slot 38).trans archive) (fun i hi => (slot i).trans (blank i hi))
      (fun i => (preserved _ (fun b => bankPool b 6 i)).trans (poolFree i))
      (fun i => (preserved _ (fun b => bankRank b 6 i)).trans (rankFree i))
      (fun i => (preserved _ (fun b => bankCoord b 6 i)).trans (coordFree i))
      (fun i hi => (preserved _ (fun b => bankMask b 6 i)).trans (maskFree i hi))
      ((congrArg List.length (preserved _ (fun b => bankG b 6 3 (by decide)))).trans recordWidth)
      ((preserved _ (fun b => bankG b 6 0 (by decide))).trans empty)
      (fun i hi => (preserved _ (fun b => bankG b 6 i (by omega))).trans (fresh i hi))
      (fun i hi => (preserved _ (fun b => bankS b 6 i hi)).trans (spare i hi)) record row len rowLen transposeReady
    exact ⟨y,l,hy,hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_right volume (bound r)) _),by rw [show (sweepRoleTape.trans owners) r = bank r 6 from (ownerPort r).symm]; exact pass⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
