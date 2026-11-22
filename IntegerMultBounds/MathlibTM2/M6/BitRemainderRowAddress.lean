module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderHandoffRow

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRadixWord
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! The forward and reverse rotation offsets of the ordinary identity row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine.FlatCoordinateLayout
open IntegerMultBounds.MathlibTM2 Cover M8.AtomOps
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem identityRow_address {M : ℕ} [NeZero M] (hm : 1 < M) :
    (LabelAddress.address (1 : Matrix (Fin 64) (Fin 64) (ZMod M))).val =
      ∑ i : Fin 64, (M^65)^i.val := by
  have reverse (i j : Fin 64) : (finProdFinEquiv (i,j)).rev = finProdFinEquiv (i.rev,j.rev) := by
    apply Fin.ext
    simp [finProdFinEquiv,Fin.val_rev]
    omega
  let digit := fun i : Fin (64*64) => ((refine (Route.cols (1 : Matrix (Fin 64) (Fin 64) (ZMod M)))) i.rev).val * M^i.val
  change (finFunctionFinEquiv _).val = _
  rw [finFunctionFinEquiv_apply]
  simp only [finEquiv_symm_val]
  change ∑ i, digit i = _
  rw [← finProdFinEquiv.sum_comp digit,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_eq_single i]
  · change ((1 : Matrix (Fin 64) (Fin 64) (ZMod M)) (finProdFinEquiv.symm (finProdFinEquiv (i,i)).rev).2
        (finProdFinEquiv.symm (finProdFinEquiv (i,i)).rev).1).val * M^_ = _
    rw [reverse i i,Equiv.symm_apply_apply,Matrix.one_apply_eq,ZMod.val_one'' (by omega : M ≠ 1),Nat.one_mul]
    rw [← pow_mul]
    congr 1
    change i.val+64*i.val = 65*i.val
    omega
  · intro j hj
    have diff : j.rev ≠ i.rev := fun eq => hj (by simpa using congrArg Fin.rev eq)
    simp [digit,reverse,refine,Route.cols,Matrix.one_apply,diff]

/-- Append a diagonal one after each block of 65 radix positions. -/
def diagonalPrefix (base : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => base * diagonalPrefix base n + 1

theorem diagonalPrefix_sum (base n : ℕ) : diagonalPrefix base n = ∑ i : Fin n, base^i.val := by
  induction n with
  | zero => simp [diagonalPrefix]
  | succ n ih =>
    rw [diagonalPrefix,ih,Fin.sum_univ_succ,Finset.mul_sum]
    simp only [Fin.val_zero,pow_zero,Fin.val_succ,pow_succ,Nat.mul_comm base,Nat.add_comm 1]

/-- In radix q the identity address repeats one digit followed by a fixed
number of zeroes. Extra leading zeroes in the last block do not affect it. -/
def diagonalDigits {q : ℕ} [NeZero q] (gap : ℕ) : ℕ → List (Fin q)
  | 0 => []
  | n+1 => 1 :: (List.replicate gap 0 ++ diagonalDigits gap n)

theorem diagonalDigits_value {q : ℕ} [NeZero q] (hq : 1 < q) (gap n : ℕ) :
    Machine.RadixDigits.value (diagonalDigits (q := q) gap n) = diagonalPrefix (q^(gap+1)) n := by
  have zeros (k : ℕ) (xs : List (Fin q)) :
      Machine.RadixDigits.value (List.replicate k 0 ++ xs) = q^k * Machine.RadixDigits.value xs := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.replicate_succ,Machine.RadixDigits.value,ih,pow_succ',Nat.mul_assoc]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [diagonalDigits,Machine.RadixDigits.value,zeros,ih,diagonalPrefix,pow_succ',Nat.mul_assoc]
    rw [show (1 : Fin q).val = 1 from Nat.mod_eq_of_lt hq,Nat.add_comm]

theorem diagonalDigits_length {q : ℕ} [NeZero q] (gap n : ℕ) :
    (diagonalDigits (q := q) gap n).length = n*(gap+1) := by
  induction n with
  | zero => simp [diagonalDigits]
  | succ n ih => simp [diagonalDigits,ih,Nat.succ_mul]; omega

local instance : NeZero prime := ⟨IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.ne_zero⟩

open IntegerMultBounds.Machine Stack Host

/-- Each scan of the precision clock prepends a block of zero digits. Replace
its low digit by one to place the next diagonal entry. -/
def writeDiagonal {T Q q : ℕ} [NeZero q] {P U : Type} (clock dst tmp : Fin T) : ℕ → Pr P T Q q U
  | 0 => .act .done
  | n+1 => (writeDiagonal clock dst tmp n).seq ((Node.umulSym 65 (RadixDigits.digitSymbol 0) clock dst tmp).seq
      (.act (.pop (.rt dst) (fun v _ => v) (.push (.rt dst) (fun _ => RadixDigits.digitSymbol 1) .done))))

theorem writeDiagonal_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {clock dst tmp : Fin T} (regs : [clock,dst,tmp].Nodup) (n w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (width : (S.R clock).length = w+1) (blank : S.R tmp = []) :
    ∃ z, z.user = u.user ∧ Exec body (writeDiagonal clock dst tmp n) (mk u S)
      (1+n*(4*(w+1)+5)) (mk z {S with R := Function.update S.R dst ((diagonalDigits (65*(w+1)-1) n).map RadixDigits.digitSymbol ++ S.R dst)}) := by
  regs_ne regs
  induction n with
  | zero =>
    exact ⟨u,rfl,by simpa [writeDiagonal,diagonalDigits,Action.run] using Exec.act (body := body) .done (mk u S)⟩
  | succ n ih =>
    obtain ⟨v,vu,rec⟩ := ih
    let ds := (diagonalDigits (q := prime) (65*(w+1)-1) n).map RadixDigits.digitSymbol
    let D : Stacks T prime := {S with R := Function.update S.R dst (ds ++ S.R dst)}
    obtain ⟨z,zv,fill⟩ := Node.umulSym_exec body 65 (RadixDigits.digitSymbol 0)
      ‹clock ≠ dst› ‹clock ≠ tmp› ‹dst ≠ tmp› v D (by simp [D,Ne.symm ‹dst ≠ tmp›,blank])
    rw [show (D.R clock).length = w+1 by simp [D,‹clock ≠ dst›,width]] at fill
    let gap := 65*(w+1)-1
    rw [show 65*(w+1) = gap+1 by dsimp [gap]; omega,List.replicate_succ] at fill
    refine ⟨z,zv.trans vu,(Exec.seq rec (Exec.seq fill (Exec.act (body := body) _ _))).cast (by simp [Nat.succ_mul]; omega) ?_⟩
    simp [Action.run,update_rt,D,ds,diagonalDigits,List.map_replicate,List.append_assoc,gap]

open IntegerMultBounds.Machine Stack Host in
theorem forwardOffset_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 6 ↪ Fin T) (w H : ℕ) (pos : 0 < H) (u : HS T Q prime U) (S : Stacks T prime)
    (digits : S.R (r 0) = (diagonalDigits (65*(w+1)-1) 64).map RadixDigits.digitSymbol)
    (width : (S.R (r 4)).length = H) (empty : S.R (r 2) = [])
    (free : ∀ i : Fin 6, i = 1 ∨ i = 3 ∨ i = 5 → S.R (r i) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ (4*H+4) + (64*(65*(w+1))*(7*H+prime+15)+4) ∧
      Exec body ((bzero (r 4) (r 2) (r 5)).seq (Fallback.radixWord r)) (mk u S) n (mk z {S with R := Function.update S.R (r 2) (binSyms H (diagonalPrefix ((prime^(w+1))^65) 64))}) := by
  have gap : 65*(w+1)-1+1 = 65*(w+1) := by omega
  have power : prime^(65*(w+1)) = (prime^(w+1))^65 := by rw [Nat.mul_comm 65,pow_mul]
  obtain ⟨v,vu,init⟩ := bzero_exec body (wR := r 4) (c := r 2) (t := r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff]) u S (free 5 (by decide))
  rw [width,empty,List.append_nil] at init
  let D : Stacks T prime := {S with R := Function.update S.R (r 2) (binSyms H 0)}
  have keep (i : Fin 6) (h : i ≠ 2) : D.R (r i) = S.R (r i) :=
    Function.update_of_ne (r.injective.ne h) _ _
  obtain ⟨z,n,zv,time,run⟩ := Fallback.radixWord_exec body r _ H pos v D
    ((keep 0 (by decide)).trans digits) (by rwa [keep 4 (by decide)]) (Function.update_self ..)
    (fun i hi => (keep i (by rcases hi with h|h|h <;> subst i <;> decide)).trans (free i hi))
  simp only [diagonalDigits_length,gap] at time
  simp only [diagonalDigits_value IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.one_lt,
    gap,power,D,Function.update_idem] at run
  exact ⟨z,_,zv.trans vu,Nat.add_le_add_left time _,Exec.seq init run⟩

/-- Generate the identity address from the precision clock and the row-count
word, releasing the digit tape after conversion. -/
theorem generateForwardOffset_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 7 ↪ Fin T) :
    ∃ code, ∀ (w H : ℕ) (_ : 0 < H) (u : HS T Q prime U) (S : Stacks T prime),
      (S.R (r 6)).length = w+1 → (S.R (r 4)).length = H →
      (∀ i : Fin 7, i ≠ 4 → i ≠ 6 → S.R (r i) = []) →
      ∃ z n, z.user = u.user ∧ n ≤ 1+64*(4*(w+1)+5) + (4*H+4) +
        64*(65*(w+1))*(7*H+prime+17)+6 ∧ Exec body code (mk u S) n
        (mk z {S with R := Function.update S.R (r 2) (binSyms H (diagonalPrefix ((prime^(w+1))^65) 64))}) := by
  let bank := (Fin.castAddEmb 1 (n := 6)).trans r
  refine ⟨(writeDiagonal (r 6) (r 0) (r 5) 64).seq
    (((bzero (bank 4) (bank 2) (bank 5)).seq (Fallback.radixWord bank)).seq (bclear (r 0))),?_⟩
  intro w H pos u S clock width free
  obtain ⟨v,vu,write⟩ := writeDiagonal_exec body (by simp [List.nodup_cons,r.injective.eq_iff] :
    [r 6,r 0,r 5].Nodup) 64 w u S clock (free 5 (by decide) (by decide))
  rw [free 0 (by decide) (by decide),List.append_nil] at write
  let ds := (diagonalDigits (q := prime) (65*(w+1)-1) 64).map RadixDigits.digitSymbol
  let D : Stacks T prime := {S with R := Function.update S.R (r 0) ds}
  have keep (i : Fin 7) (hi : i ≠ 0) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) _ _
  obtain ⟨y,n,yv,time,convert⟩ := forwardOffset_exec body bank w H pos v D (Function.update_self ..)
    (by change (D.R (r 4)).length = H; rwa [keep 4 (by decide)]) ((keep 2 (by decide)).trans (free 2 (by decide) (by decide))) (by
      intro i hi
      rcases hi with h|h|h <;> subst i <;> exact (keep _ (by decide)).trans (free _ (by decide) (by decide)))
  let word := binSyms (A := prime) H (diagonalPrefix ((prime^(w+1))^65) 64)
  let E : Stacks T prime := {D with R := Function.update D.R (r 2) word}
  obtain ⟨z,zy,_,clear⟩ := bclear_exec body (r 0) y E
  have len : (E.R (r 0)).length = 64*(65*(w+1)) := by
    simp [E,D,r.injective.eq_iff,ds,diagonalDigits_length,show 65*(w+1)-1+1 = 65*(w+1) by omega]
  have final : Function.update E.R (r 0) [] = Function.update S.R (r 2) word := by
    funext j
    by_cases h : j = r 0 <;> by_cases k : j = r 2 <;>
      simp_all [E,D,Function.update_of_ne,r.injective.eq_iff]
  rw [len,final] at clear
  exact ⟨z,_,zy.trans (yv.trans vu),by nlinarith only [time],Exec.seq write (Exec.seq convert clear)⟩

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- One natural-number computation supplies both signed rotation headers. -/
theorem ordinaryRotationOffsets (w : ℕ) :
    let M := prime^(w+1)
    let offset := diagonalPrefix (M^65) 64
    let row := LabelAddress.address (1 : LabelPadding.Label 64 (w+1))
    (ordinaryIdentityRow (w+1)).val = offset ∧ (0-row).val = M^(64*64)-offset := by
  intro M offset row
  have fwd : row.val = offset := (identityRow_address (M := M)
    (one_lt_pow₀ IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.one_lt (by omega))).trans
      (diagonalPrefix_sum _ _).symm
  have pos : 0 < offset := Nat.zero_lt_succ _
  have nz : row ≠ 0 := Fin.val_ne_zero_iff.mp (fwd.trans_ne pos.ne')
  constructor
  · unfold ordinaryIdentityRow
    rw [Fin.val_cast]
    exact fwd
  · rw [zero_sub,Fin.val_neg,if_neg nz,fwd]

end IntegerMultBounds.MathlibTM2.M6.BitNode
