module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepPlacedChart
public import IntegerMultBounds.MathlibTM2.DFT.Fields

/-! Initialize both physical rank matrices using one pool of arithmetic frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl
open Cover.Fallback RingFormula Host Stack Node Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

private def archivePorts : Fin 7 ↪ Fin 39 := ⟨![1,37,38,2,3,4,6],by decide⟩

private def withPredClock {P U : Type} {T Q A : ℕ} (src pred tmp : Fin T) (writer : Pr P T Q A U) :
    Pr P T Q A U := .seq (ucopy src pred tmp) (.seq (.act (DFT.dropR pred)) (.seq writer (uclear pred)))

private theorem withPredClock_writes {P U : Type} {T Q A : ℕ} (body : P → Pr P T Q A U)
    (src pred tmp out : Fin T) (sep : [src,pred,tmp].Nodup) (apart : pred ≠ out)
    (w cost : ℕ) (ready : Regs T A → Prop) (writer : Pr P T Q A U) (word : List (Fin (A+4)))
    (write : Writes body ready out writer word cost) :
    Writes body (fun R => (R src).length = w+1 ∧ R pred = [] ∧ R tmp = [] ∧
      ready (Function.update R pred (List.replicate w tick))) out
      (withPredClock src pred tmp writer) word (cost+6*w+11) := by
  intro v S ⟨width,empty,scratch,valid⟩
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or,List.not_mem_nil,
    not_false_eq_true,List.nodup_nil,and_true] at sep
  obtain ⟨u,hu,copy⟩ := ucopy_exec body sep.1.1 sep.1.2 sep.2 v S scratch
  rw [width,empty,List.append_nil] at copy
  let B := {S with R := Function.update S.R pred (List.replicate (w+1) tick)}
  have drop := Exec.act (body := body) (DFT.dropR pred) (mk u B)
  rw [DFT.dropR_run] at drop
  simp only [B,Function.update_self,List.replicate_succ,List.tail_cons,Function.update_idem] at drop
  let F := {S with R := Function.update S.R pred (List.replicate w tick)}
  obtain ⟨y,k,hy,hk,run⟩ := write u F valid
  let E := {F with R := Function.update F.R out (word ++ F.R out)}
  obtain ⟨z,hz,clear⟩ := uclear_exec body pred y E
  have len : (E.R pred).length = w := by simp [E,F,apart]
  have final : {E with R := Function.update E.R pred []} = {S with R := Function.update S.R out (word ++ S.R out)} := by
    congr 1
    funext i
    by_cases h : i = pred
    · subst i; simp [apart,empty]
    · simp [E,F,Function.update_apply,h,apart.symm]
  rw [final,len] at clear
  exact ⟨z,_,hz.trans (hy.trans hu),by omega,Exec.seq copy (Exec.seq drop (Exec.seq run clear))⟩

theorem sweepPlacedMatrices_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) :
    ∃ C : ℕ, ∀ (p : Fin 39 ↪ Fin T) (pool : Fin ((sweepMatrixDepth+1)*13) ↪ Fin T),
    (∀ i j, p i ≠ pool j) → ∀ (n : Fin 9) (r : Role), ∃ program : Pr P T Q prime U,
    ∀ w H (parent : Fin 64 → ZMod (prime^(w+1))) (tail : List (Fin (prime+4))) (v : HS T Q prime U) (S : Stacks T prime),
    let M := prime^(w+1)
    let N := M^128
    let last : Fin N := ⟨N-1,by have := pow_pos (pow_pos prime_prime.pos (w+1)) 128; dsimp [N,M]; omega⟩
    let mat := sweepRankMatrices (w+1) parent n r last
    N < 2^H → H ≤ N+1 → (S.R (p 10)).length = w+1 → S.R (p 20) = binSyms H 0 →
    S.R (p 33) = binSyms H (1 : ZMod M).val → S.R (p 36) = binSyms H M →
    (S.R (p 18)).length = H → (S.R (p 37)).length = M.size →
    S.R (p 38) = (List.ofFn fun j => binSyms M.size (parent j).val).flatten ++ tail →
    (∀ i ∈ ([1,2,3,4,6,8,9,11,12,13,14,15,16,17,19,25,26,27] : List (Fin 39)), S.R (p i) = []) →
    (∀ j, S.R (pool j) = []) →
    ∃ z t, z.user = v.user ∧ t ≤ C*N^3 ∧ Exec body program (mk v S) t (mk z {S with
      R := Function.update (Function.update S.R (p 28) (matrixWords prime H (mat false) ++ S.R (p 28)))
        (p 22) (matrixWords prime H (mat true) ++ S.R (p 22))}) := by
  obtain ⟨I,_,depth,_,negative,budget⟩ := sweepMatrixSetup_budget.choose_spec
  obtain ⟨K,charts⟩ := sweepPlacedChart_writes body
  refine ⟨K+6+17+I,?_⟩
  intro p pool off n r
  let base := (Fin.castLEEmb (by decide : 37 ≤ 39)).trans p
  let c := sweepLiteralPorts.trans base
  let a := archivePorts.trans p
  obtain ⟨chart,writeChart⟩ := charts base pool (fun i j => off _ _) n r
  obtain ⟨input,writeInput⟩ := sweepInitialMatrix_writes body pool c a (p 18) (p 22)
    (fun i j => off _ _) (fun i => p.injective.ne (by decide +revert)) (fun j => (off _ j).symm)
    (fun i => p.injective.ne (by decide +revert)) (fun i => p.injective.ne (by decide +revert))
    (p.injective.ne (by decide)) depth negative
  refine ⟨.seq (withPredClock (p 10) (p 27) (p 1) chart) input,?_⟩
  intro w H parent tail v S M N last mat fits field ticks zeroWord oneWord modulus bits size archive blank free
  have clocked := withPredClock_writes body (p 10) (p 27) (p 1) (p 28)
    (by simp [List.nodup_cons]) (by simp) w _ _ _ _ (writeChart w H parent last fits field)
  obtain ⟨u,k,hu,hk,emitChart⟩ := clocked v S ⟨ticks,blank _ (by decide),blank _ (by decide),by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · change (Function.update S.R (p 27) _ (p 27)).length = w
      simp
    · exact (Function.update_of_ne (p.injective.ne (by decide : (20 : Fin 39) ≠ 27)) _ _).trans zeroWord
    · exact (Function.update_of_ne (p.injective.ne (by decide : (33 : Fin 39) ≠ 27)) _ _).trans oneWord
    · exact (Function.update_of_ne (p.injective.ne (by decide : (36 : Fin 39) ≠ 27)) _ _).trans modulus
    · intro i hi
      exact (Function.update_of_ne (p.injective.ne (by decide +revert)) _ _).trans (blank _ (by decide +revert))
    · intro j; exact (Function.update_of_ne (off 27 j).symm _ _).trans (free j)⟩
  let B := {S with R := Function.update S.R (p 28) (matrixWords prime H (mat false) ++ S.R (p 28))}
  have keep (i : Fin 39) (hi : i ≠ 28) : B.R (p i) = S.R (p i) := Function.update_of_ne (p.injective.ne hi) _ _
  have fresh (i : Fin 39) (hi : i ∈ ([1,2,3,4,6] : List (Fin 39))) : B.R (p i) = [] :=
    (keep i (by decide +revert)).trans (blank i (by decide +revert))
  obtain ⟨z,l,hz,hl,emitInput⟩ := writeInput (w+1) H parent n r tail fits u B
    ⟨⟨(keep 20 (by decide)).trans zeroWord,(keep 33 (by decide)).trans oneWord,(keep 36 (by decide)).trans modulus,
      fun i hi => fresh _ (by decide +revert),fun j => (Function.update_of_ne (off 28 j).symm _ _).trans (free j)⟩,
      (keep 38 (by decide)).trans archive,(congrArg List.length (keep 37 (by decide))).trans size,(congrArg List.length (keep 18 (by decide))).trans bits,
      fun i hi => fresh _ (by decide +revert)⟩
  have total := budget n r w H fits field
  have bill : l ≤ I*N^3 := by dsimp only [N,M]; dsimp only [sweepMatrixDepth] at hl total; omega
  change k ≤ (K+6)*N^3+6*w+11 at hk
  have wn : w+1 ≤ N := (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left prime_prime.two_le (w+1))).trans
    (Nat.le_self_pow (by decide : 128 ≠ 0) M)
  have hn := Nat.le_self_pow (by decide : 3 ≠ 0) N
  have clockBill : k ≤ (K+6+17)*N^3 := by rw [Nat.add_mul]; omega
  refine ⟨z,k+l,hz.trans hu,by rw [Nat.add_mul]; exact Nat.add_le_add clockBill bill,Exec.seq emitChart ?_⟩
  change Exec body input (mk u B) l (mk z {B with R := Function.update B.R (p 22) (matrixWords prime H (mat true) ++ S.R (p 22))})
  simpa only [keep 22 (by decide)] using emitInput

end IntegerMultBounds.MathlibTM2.M6.BitNode
