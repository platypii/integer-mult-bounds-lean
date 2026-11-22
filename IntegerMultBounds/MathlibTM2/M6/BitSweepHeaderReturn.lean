module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepGeneratedReturn
public import IntegerMultBounds.MathlibTM2.M6.BitSweepHeaders

/-! Return records to node order directly from the unary block headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Routing RadixDigits RadixCounterData Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepHeaderReturn_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 39 ↪ Fin T) (pool : Fin ((sweepMatrixDepth+1)*13) ↪ Fin T)
    (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T) (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j) (off : ∀ i j, p i ≠ pool j)
    (hr : ∀ i j, p i ≠ rankPool j) (hc : ∀ i j, p i ≠ coordPool j)
    (rg : BinaryMaskReg ↪ Fin T) (g : Fin 10 ↪ Fin T) (sharedWidth : rg .width = p 35)
    (maskOff : ∀ i j, j ≠ .width → p i ≠ rg j) (sharedCount : g 4 = p 7)
    (gOff : ∀ i j, i ≠ 4 → g i ≠ p j) (outMask : ∀ j, g 0 ≠ rg j)
    (bank : Fin 8 ↪ Fin T) (maskPort : bank 6 = g 0)
    (unitPort : bank 4 = p 29) (countPort : bank 7 = p 7)
    (bankOff : ∀ i j, i ≠ 4 → i ≠ 7 → bank i ≠ p j) (n : Fin 9) (role : Role) :
    ∃ (program : Pr P T Q prime U) (C : ℕ), ∀ (w H W : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
      (units : ∀ i, IsUnit (parent i)) (archiveTail : List (Fin (prime+4))),
    let M := prime^(w+1)
    let N := M^128
    N < 2^H → H ≤ N+1 → ∀ (rows : Fin N → List (Fin (prime+4))) (tail : List (Fin (prime+4))),
    (∀ i, (rows i).length = W) →
    Writes body (fun R => (R (p 10)).length = w+1 ∧ (R (p 18)).length = H ∧ (R (p 29)).length = 1 ∧
      (R (p 37)).length = M.size ∧ R (p 38) = (List.ofFn fun i => binSyms M.size (parent i).val).flatten ++ archiveTail ∧
      (∀ i ∈ ([0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,17,19,20,21,22,23,25,26,27,28,30,31,32,33,34,35,36] : List (Fin 39)), R (p i) = []) ∧
      (∀ j, R (pool j) = []) ∧ (∀ j, R (rankPool j) = []) ∧ (∀ j, R (coordPool j) = []) ∧
      (∀ j, j ≠ .width → R (rg j) = []) ∧ R (g 2) = (List.ofFn fun j => rows (nodeSourceRank (w+1) parent units n role j)).flatten ++ tail ∧
      (R (g 3)).length = W ∧ R (g 0) = [] ∧ (∀ i : Fin 10, 5 ≤ i → R (g i) = []) ∧
      ∀ i : Fin 8, i ≠ 4 → i ≠ 7 → R (bank i) = [])
      (g 1) program (List.ofFn rows).flatten
      (C*N^3+N*(N*(16*W+18)+26)+2) := by
  let base := (Fin.castLEEmb (by decide : 37 ≤ 39)).trans p
  have sep (i : Fin 39) (hi : i ∈ ([1,2,22,28] : List (Fin 39))) (j) : p i ≠ rg j := by
    by_cases h : j = .width
    · subst j; rw [sharedWidth]; exact p.injective.ne (by clear * - hi; decide +revert)
    · exact maskOff i j h
  have gather (i : Fin 10) : g i ≠ p 22 ∧ g i ≠ p 28 := by
    by_cases h : i = 4
    · subst i; simp [sharedCount]
    · exact ⟨gOff _ _ h,gOff _ _ h⟩
  obtain ⟨worker,K,block⟩ := sweepGeneratedReturn_exec body p pool rankPool coordPool disjoint off hr hc rg g sep
    (fun j => gOff 0 j (by decide)) gather outMask bank maskPort (by
      intro i
      by_cases h : i = 4
      · subst i; simp [unitPort]
      by_cases h' : i = 7
      · subst i; simp [countPort]
      exact ⟨bankOff i _ h h',bankOff i _ h h'⟩) n role
  obtain ⟨program,headers⟩ := withSweepHeaders_writes body base (g 1) (fun i _ => gOff 1 _ (by decide)) worker
  refine ⟨program,K+1500,?_⟩
  intro w H W parent units archiveTail M N fits field rows tail sizes v S
    ⟨exponent,bits,unit,size,archive,blank,poolFree,rankFree,coordFree,maskFree,data,record,empty,fresh,bankFree⟩
  let word := (List.ofFn rows).flatten
  let cost := K*N^3+N*(N*(16*W+18)+26)+2
  let ok := fun R => ∀ (u : HS T Q prime U) (B : Stacks T prime), B.R = R →
    ∃ y l, y.user = u.user ∧ l ≤ cost ∧ Exec body worker (mk u B) l
      (mk y {B with R := Function.update B.R (g 1) (word ++ B.R (g 1))})
  obtain ⟨z,k,hz,hk,run⟩ := headers (w+1) H cost word ok (by omega) fits field (fun u B h => h u B rfl)
    v S ⟨exponent,bits,unit,fun i hi => blank _ (by decide +revert),by
      intro u B eqn
      let installed := (sweepHeaderWords (w+1) H).foldl (fun R (kv : Fin 37 × List (Fin (prime+4))) =>
        Function.update R (base kv.1) kv.2) S.R
      change B.R = installed at eqn
      have keep (j : Fin T) (hj : ∀ i ∈ sweepHeaderPorts, j ≠ base i) : B.R j = S.R j := by
        rw [eqn]
        simp [installed,sweepHeaderWords,hj _ (by decide : (5 : Fin 37) ∈ sweepHeaderPorts),
          hj _ (by decide : (0 : Fin 37) ∈ sweepHeaderPorts),hj _ (by decide : (7 : Fin 37) ∈ sweepHeaderPorts),
          hj _ (by decide : (21 : Fin 37) ∈ sweepHeaderPorts),hj _ (by decide : (35 : Fin 37) ∈ sweepHeaderPorts),
          hj _ (by decide : (36 : Fin 37) ∈ sweepHeaderPorts),hj _ (by decide : (34 : Fin 37) ∈ sweepHeaderPorts),
          hj _ (by decide : (20 : Fin 37) ∈ sweepHeaderPorts),hj _ (by decide : (33 : Fin 37) ∈ sweepHeaderPorts)]
      have slot (i : Fin 39) (hi : i ∉ ([5,0,7,21,35,36,34,20,33] : List (Fin 39))) : B.R (p i) = S.R (p i) :=
        keep _ (fun j hj => p.injective.ne (by clear * - hi hj; decide +revert))
      have gg (i : Fin 10) (hi : i ≠ 4) := keep (g i) (fun j _ => gOff i _ hi)
      have baseWord : 1 < M := Nat.one_lt_pow (by omega) prime_prime.one_lt
      have single : (1 : ZMod M).val = 1 := by
        simpa using (ZMod.val_natCast_of_lt baseWord)
      refine block w H parent units archiveTail u B fits field ?_ ?_ ?_
        ((congrArg List.length (slot 10 (by decide))).trans exponent)
        ((congrArg List.length (slot 18 (by decide))).trans bits) ?_ ?_ ?_ ?_ ?_ ?_
        ((congrArg List.length (slot 37 (by decide))).trans size) ((slot 38 (by decide)).trans archive)
        (fun i hi => (slot i (by clear * - hi; decide +revert)).trans (blank i (by clear * - hi; decide +revert)))
        (fun j => (keep _ (fun i _ => (off _ j).symm)).trans (poolFree j))
        (fun j => (keep _ (fun i _ => (hr _ j).symm)).trans (rankFree j))
        (fun j => (keep _ (fun i _ => (hc _ j).symm)).trans (coordFree j))
        ⟨?_,fun j hj => (keep _ (fun i _ => (maskOff _ j hj).symm)).trans (maskFree j hj)⟩
        W rows tail (B.R (p 29)) (B.R (p 7))
        ((congrArg List.length (slot 29 (by decide))).trans unit) ?_ (by
          refine Stacks.ext rfl rfl rfl ?_
          funext i
          have free (j : Fin 8) (h : j ≠ 4) (d : j ≠ 7) : B.R (bank j) = [] :=
            (keep _ (fun k _ => bankOff j _ h d)).trans (bankFree j h d)
          fin_cases i <;> first | exact free _ (by decide) (by decide) |
            simp [embStk,transposeStacks,unitPort,countPort]) sizes ((gg 2 (by decide)).trans data) ?_
        ((congrArg List.length (gg 3 (by decide))).trans record) ((gg 0 (by decide)).trans empty)
        (fun i hi => (gg i (by omega)).trans (fresh i hi))
      all_goals simp [sharedCount,sharedWidth,eqn,installed,sweepHeaderWords,base,N,M,
        ZMod.val_one_eq_one_mod,Nat.mod_eq_of_lt baseWord,length_binSyms]
      ⟩
  have volume := Nat.le_self_pow (by decide : 3 ≠ 0) N
  exact ⟨z,k,hz,by change k ≤ cost+1500*N at hk; dsimp only [cost] at hk; rw [Nat.add_mul]; omega,run⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
