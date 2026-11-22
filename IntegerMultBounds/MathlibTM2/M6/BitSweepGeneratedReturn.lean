module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepPlacedMatrices
public import IntegerMultBounds.MathlibTM2.M6.BitSweepPhysicalReturn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRewind

/-! Restore node record order from the parent's packed weights. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Shared50ModularControl Cover.Fallback RingFormula Stack Host Node Routing RadixDigits RadixCounterData
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepGeneratedReturn_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (p : Fin 39 ↪ Fin T) (pool : Fin ((sweepMatrixDepth+1)*13) ↪ Fin T)
    (rankPool : Fin ((sweepBinaryRankCode.depth+1)*13) ↪ Fin T) (coordPool : Fin ((sweepCoordDepth+1)*13) ↪ Fin T)
    (disjoint : ∀ i j, coordPool i ≠ rankPool j) (off : ∀ i j, p i ≠ pool j)
    (hr : ∀ i j, p i ≠ rankPool j) (hc : ∀ i j, p i ≠ coordPool j)
    (rg : BinaryMaskReg ↪ Fin T) (g : Fin 10 ↪ Fin T) (maskOff : ∀ i ∈ ([1,2,22,28] : List (Fin 39)), ∀ j, p i ≠ rg j)
    (outOff : ∀ j, g 0 ≠ p j) (gOff : ∀ i, g i ≠ p 22 ∧ g i ≠ p 28) (outMask : ∀ j, g 0 ≠ rg j)
    (bank : Fin 8 ↪ Fin T) (shared : bank 6 = g 0)
    (bankOff : ∀ i, bank i ≠ p 22 ∧ bank i ≠ p 28) (n : Fin 9) (role : Role) :
    ∃ (program : Pr P T Q prime U) (C : ℕ), ∀ (w H : ℕ) (parent : Fin 64 → ZMod (prime^(w+1)))
      (units : ∀ i, IsUnit (parent i)) (archiveTail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime),
    let M := prime^(w+1)
    let N := M^128
    N < 2^H → H ≤ N+1 → (S.R (p 7)).length = N →
    S.R (p 0) = (zeros prime_prime.two_le ((w+1)*128)).map digitSymbol →
    (S.R (p 5)).length = (w+1)*128 → (S.R (p 10)).length = w+1 → (S.R (p 18)).length = H →
    (S.R (p 21)).length = 128*H → S.R (p 35) = binSyms H N → S.R (p 36) = binSyms H M →
    S.R (p 20) = binSyms H 0 → S.R (p 33) = binSyms H (1 : ZMod M).val →
    S.R (p 34) = binSyms H (M : ZMod N).val → (S.R (p 37)).length = M.size →
    S.R (p 38) = (List.ofFn fun j => binSyms M.size (parent j).val).flatten ++ archiveTail →
    (∀ i ∈ ([1,2,3,4,6,8,9,11,12,13,14,15,16,17,19,22,23,25,26,27,28,30,31,32] : List (Fin 39)), S.R (p i) = []) →
    (∀ j, S.R (pool j) = []) → (∀ j, S.R (rankPool j) = []) → (∀ j, S.R (coordPool j) = []) →
    DescriptorCompileReady rg S.R H N →
    ∀ (W : ℕ) (rows : Fin N → List (Fin (prime+4))) (tail unit row : List (Fin (prime+4))),
    unit.length = 1 → row.length = N →
    embStk bank S = transposeStacks (embStk bank S) [] [] [] unit row →
    (∀ i, (rows i).length = W) → S.R (g 2) = (List.ofFn (fun j => rows (nodeSourceRank (w+1) parent units n role j))).flatten ++ tail →
    (S.R (g 4)).length = N → (S.R (g 3)).length = W → S.R (g 0) = [] →
    (∀ i : Fin 10, 5 ≤ i.val → S.R (g i) = []) →
    ∃ z t, z.user = v.user ∧ t ≤ C*N^3+N*(N*(16*W+18)+26)+2 ∧ Exec body program (mk v S) t (mk z {S with
      R := Function.update S.R (g 1) ((List.ofFn rows).flatten ++ S.R (g 1))}) := by
  let base := (Fin.castLEEmb (by decide : 37 ≤ 39)).trans p
  obtain ⟨I,build⟩ := sweepPlacedMatrices_exec body
  obtain ⟨setup,prepare⟩ := build p pool off n role
  obtain ⟨permute,K,block⟩ := sweepPhysicalReturn_exec body base rankPool coordPool disjoint
    (fun i => hr _) (fun i => hc _) rg g (fun i hi => maskOff _ (by decide +revert)) (fun i => outOff _) outMask bank shared n role
  refine ⟨.seq setup (.seq permute (.seq (bclear (p 22)) (bclear (p 28)))),I+K+32772,?_⟩
  intro w H parent units archiveTail v S M N fits field ticks counter digits exponent bits clock rankWord modulus zeroWord oneWord
    radix size archive blank poolFree rankFree coordFree ready W rows tail unit row unitLen rowLen prepared sizes data count record empty fresh
  let last : Fin N := ⟨N-1, by have := pow_pos (pow_pos prime_prime.pos (w+1)) 128; dsimp [N,M]; omega⟩
  let words := fun b => matrixWords prime H (sweepRankMatrices (w+1) parent n role last b)
  obtain ⟨u,k,hu,hk,init⟩ := prepare w H parent archiveTail v S fits field exponent zeroWord oneWord modulus
    bits size archive (fun i hi => blank i (by decide +revert)) poolFree
  rw [blank 22 (by decide),blank 28 (by decide),List.append_nil,List.append_nil] at init
  let B := {S with R := Function.update (Function.update S.R (p 28) (words false)) (p 22) (words true)}
  have keep (i) (a : i ≠ p 22) (b : i ≠ p 28) : B.R i = S.R i := by simp [B,a,b]
  have slot (i : Fin 39) (a : i ≠ 22) (b : i ≠ 28) := keep (p i) (p.injective.ne a) (p.injective.ne b)
  have gather i := keep (g i) (gOff i).1 (gOff i).2
  have mask i := keep (rg i) (maskOff 22 (by decide) i).symm (maskOff 28 (by decide) i).symm
  have read (i : Fin 39) (a : i ≠ 22) (b : i ≠ 28) := congrArg List.length (slot i a b)
  obtain ⟨y,l,hy,hl,run⟩ := block (w+1) H parent units [] u B (by omega) fits
    ((read 7 (by decide) (by decide)).trans ticks) ((slot 0 (by decide) (by decide)).trans counter)
    ((read 5 (by decide) (by decide)).trans digits) ((read 10 (by decide) (by decide)).trans exponent)
    ((read 18 (by decide) (by decide)).trans bits) ((read 21 (by decide) (by decide)).trans clock)
    (by change B.R (p 22) = words true ++ []; simp [B])
    ⟨[],by change B.R (p 28) = words false ++ []; simp [B]⟩
    ((slot 35 (by decide) (by decide)).trans rankWord) ((slot 36 (by decide) (by decide)).trans modulus)
    ((slot 20 (by decide) (by decide)).trans zeroWord) ((slot 33 (by decide) (by decide)).trans oneWord)
    ((slot 34 (by decide) (by decide)).trans radix)
    (fun i hi => (slot _ (by decide +revert) (by decide +revert)).trans (blank _ (by decide +revert)))
    (fun j => (keep _ (hr 22 j).symm (hr 28 j).symm).trans (rankFree j))
    (fun j => (keep _ (hc 22 j).symm (hc 28 j).symm).trans (coordFree j))
    ((slot 8 (by decide) (by decide)).trans (blank 8 (by decide)))
    ⟨(mask _).trans ready.width,fun i hi => (mask i).trans (ready.blank i hi)⟩ field W rows tail unit row unitLen rowLen (by
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      exact (keep _ (bankOff i).1 (bankOff i).2).trans (congrArg (fun D : Stacks 8 prime => D.R i) prepared)) sizes
    ((gather 2).trans data) ((congrArg List.length (gather 4)).trans count) ((congrArg List.length (gather 3)).trans record)
    ((gather 0).trans empty) (fun i hi => (gather i).trans (fresh i hi))
  rw [gather 1] at run
  let output := (List.ofFn rows).flatten ++ S.R (g 1)
  let F := {B with R := Function.update B.R (g 1) output}
  let E := {F with R := Function.update F.R (p 22) []}
  obtain ⟨a,ha,_,clearInput⟩ := bclear_exec body (p 22) y F
  obtain ⟨z,hz,_,clearChart⟩ := bclear_exec body (p 28) a E
  have inputLen : (F.R (p 22)).length = 4096*H := by simp [F,B,(gOff 1).1.symm,words,length_matrixWords]
  have chartLen : (E.R (p 28)).length = 4096*H := by simp [E,F,B,(gOff 1).2.symm,words,length_matrixWords]
  have final : {E with R := Function.update E.R (p 28) []} = {S with R := Function.update S.R (g 1) output} := by
    congr 1
    funext i
    by_cases h : i = p 28
    · subst i; simp [(gOff 1).2.symm,blank 28 (by decide)]
    by_cases d : i = p 22
    · subst i; simp [E,(gOff 1).1.symm,blank 22 (by decide)]
    simp [E,F,B,Function.update_apply,h,d]
  rw [inputLen] at clearInput
  rw [final,chartLen] at clearChart
  change k ≤ I*N^3 at hk
  change l ≤ K*N^3+N*(N*(16*W+18)+26)+2 at hl
  have pos : 0 < N := pow_pos (pow_pos prime_prime.pos _) _
  have large := Nat.le_self_pow (by decide : 3 ≠ 0) N
  refine ⟨z,_,hz.trans (ha.trans (hy.trans hu)),?_,Exec.seq init (Exec.seq run (Exec.seq clearInput clearChart))⟩
  rw [Nat.add_mul,Nat.add_mul]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
