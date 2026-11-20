module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Pack the reciprocal of the inherited diagonal on the ordinary-record tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Cover.Fallback
variable {T Q A p w m : ℕ} {P U : Type} [NeZero (p^(w+1))]
local notation "M" => p^(w+1)

def reciprocalReadPorts : Fin 7 ↪ Fin 19 := ⟨![1,4,18,14,2,3,5],by decide⟩

def readReciprocal (p i : ℕ) (bank : Fin 19 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord i (reciprocalReadPorts.trans bank))
    (.seq (reusablePivotInverse p ((Fin.castLEEmb (by decide)).trans bank) (bank 16) (bank 17))
      (bclear (bank 14)))

theorem readReciprocal_exec (body : P → Pr P T Q A U) (bank : Fin 19 ↪ Fin T)
    (weight : Fin m → ZMod M) (i : Fin m) (unit : IsUnit (weight i)) (hp : p.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (weights : S.R (bank 18) = (List.ofFn fun j => binSyms H (weight j).val).flatten ++ tail)
    (modulus : S.R (bank 4) = binSyms H M) (one : S.R (bank 15) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 16)).length = w)
    (free : ∀ j : Fin 19, (j < 13 ∧ j ≠ 4) ∨ j = 14 ∨ j = 17 → S.R (bank j) = []) :
    let C := 48*H*H+152*H+66
    ∃ z t, z.user = v.user ∧ t ≤ (8*(i.val*H)+14*H+22) +
      (6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C))) + (2*H+2) ∧
      Exec body (readReciprocal p i.val bank) (mk v S) t
        (mk z {S with R := Function.update S.R (bank 0) (binSyms H (Ring.inverse (weight i)).val)}) := by
  intro C
  let row : Matrix (Fin 1) (Fin m) (ZMod M) := fun _ j => weight j
  have fresh : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → reciprocalReadPorts k < 13 ∧ reciprocalReadPorts k ≠ 4 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (reciprocalReadPorts.trans bank) row 0 i H v S tail
    (by change S.R (bank 18) = matrixWords A H row ++ tail; simpa [matrixWords,row,List.ofFn_succ] using weights)
    ((congrArg List.length modulus).trans (length_binSyms ..)) (fun k h => free _ (.inl (fresh k h)))
  change Exec _ (readMatrixWord (0*m+i.val) _) _ (8*((0*m+i.val)*H)+14*H+22)
    (mk u {S with R := Function.update S.R (bank 14) (binSyms H (weight i).val ++ S.R (bank 14))}) at read
  simp only [Nat.zero_mul,Nat.zero_add,free 14 (by decide),List.append_nil] at read
  let D := {S with R := Function.update S.R (bank 14) (binSyms H (weight i).val)}
  have keep (j : Fin 19) (h : j ≠ 14) : D.R (bank j) = S.R (bank j) := Function.update_of_ne (bank.injective.ne h) ..
  let r := (Fin.castLEEmb (by decide : 16 ≤ 19)).trans bank
  have apart : ∀ j : Fin 16, (Fin.castLEEmb (by decide : 16 ≤ 19)) j ≠ 17 := by decide
  have scratch : ∀ j : Fin 16, j ≠ 4 → j < 13 →
      let k := (Fin.castLEEmb (by decide : 16 ≤ 19)) j
      k ≠ 14 ∧ k < 13 ∧ k ≠ 4 := by decide
  obtain ⟨y,F,n,hy,price,run,_,word,left,input,output,frame⟩ := reusablePivotInverse_exec body p w hp _ unit
    r (bank 16) (bank 17) (by simp [r,List.nodup_cons,bank.injective.eq_iff])
    (fun j => bank.injective.ne (apart j)) H hm u D
    ((congrArg List.length (keep 16 (by decide))).trans clock) ((keep 17 (by decide)).trans (free 17 (by decide)))
    (Function.update_self ..) ((keep 15 (by decide)).trans one) ((keep 4 (by decide)).trans modulus)
    (fun j hj h => (keep _ (scratch j hj h).1).trans (free _ (.inl (scratch j hj h).2)))
  change F.R (bank 0) = _ at word
  have saved := (frame _ (bank.injective.ne (by decide : (14 : Fin 19) ≠ 0))).trans (Function.update_self ..)
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (bank 14) y F
  rw [saved,length_binSyms] at clear
  refine ⟨z,_,hz.trans (hy.trans hu),by dsimp [C]; omega,(Exec.seq read (Exec.seq run clear)).cast rfl ?_⟩
  apply congrArg (mk z)
  refine Stacks.ext input output left ?_
  funext k
  by_cases h : k = bank 14
  · subst k; simp [bank.injective.eq_iff,free 14 (by decide)]
  by_cases g : k = bank 0
  · subst k; simpa [Function.update_of_ne h] using word
  exact (Function.update_of_ne h ..).trans ((frame k g).trans ((Function.update_of_ne h ..).trans (Function.update_of_ne g ..).symm))

def packReciprocals (p : ℕ) (bank : Fin 19 ↪ Fin T) (dest : Fin T) : List (Fin m) → Pr P T Q A U
  | [] => .act .done
  | i :: rows => .seq (packReciprocals p bank dest rows)
      (.seq (readReciprocal p i.val bank) (moveRightOrdered (bank 0) (bank 1) dest))

theorem packReciprocals_exec (body : P → Pr P T Q A U) (bank : Fin 19 ↪ Fin T)
    (dest : Fin T) (outside : ∀ j, bank j ≠ dest)
    (weight : Fin m → ZMod M) (rows : List (Fin m)) (unit : ∀ i, IsUnit (weight i)) (hp : p.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (weights : S.R (bank 18) = (List.ofFn fun j => binSyms H (weight j).val).flatten ++ tail)
    (modulus : S.R (bank 4) = binSyms H M) (one : S.R (bank 15) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 16)).length = w)
    (free : ∀ j : Fin 19, (j < 13 ∧ j ≠ 4) ∨ j = 14 ∨ j = 17 → S.R (bank j) = []) :
    let C := 48*H*H+152*H+66
    let cost := fun i : Fin m => (8*(i.val*H)+14*H+22) +
      (6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C))) + (2*H+2) + (4*H+4)
    let word := fun i => binSyms (A := A) H (Ring.inverse (weight i)).val
    ∃ z t, z.user = v.user ∧ t ≤ (rows.map cost).sum+1 ∧
      Exec body (packReciprocals p bank dest rows) (mk v S) t
        (mk z {S with R := Function.update S.R dest (rows.flatMap word ++ S.R dest)}) := by
  intro C cost word
  induction rows with
  | nil =>
    exact ⟨v,1,rfl,by simp,by simpa [packReciprocals] using Exec.act (body := body) (.done) (mk v S)⟩
  | cons i rows ih =>
    obtain ⟨u,l,hu,hl,run⟩ := ih
    let D := {S with R := Function.update S.R dest (rows.flatMap word ++ S.R dest)}
    have keep (j) : D.R (bank j) = S.R (bank j) := Function.update_of_ne (outside j) ..
    obtain ⟨y,n,hy,hn,read⟩ := readReciprocal_exec body bank weight i (unit i) hp H hm u D tail
      ((keep 18).trans weights) ((keep 4).trans modulus) ((keep 15).trans one)
      ((congrArg List.length (keep 16)).trans clock) (fun j hj => (keep j).trans (free j hj))
    let E := {D with R := Function.update D.R (bank 0) (word i)}
    have different := bank.injective.ne (by decide : (1 : Fin 19) ≠ 0)
    obtain ⟨z,hz,push⟩ := moveRightOrdered_exec (body := body) (bank 0) (bank 1) dest
      different.symm (outside 0) (outside 1) y E
      ((Function.update_of_ne different ..).trans ((keep 1).trans (free 1 (by decide))))
    have loaded : E.R (bank 0) = word i := Function.update_self ..
    rw [loaded,show (word i).length = H from length_binSyms ..] at push
    refine ⟨z,_,hz.trans (hy.trans hu),?_,(Exec.seq run (Exec.seq read push)).cast rfl ?_⟩
    · simp only [List.map_cons,List.sum_cons]
      dsimp [cost,C] at *
      omega
    · apply congrArg (mk z)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hd : k = dest
      · subst k; simp [E,D,(outside 0).symm,List.append_assoc]
      by_cases h0 : k = bank 0
      · subst k; simp [Function.update_of_ne hd,free 0 (by decide)]
      simp [E,D,Function.update_of_ne hd,Function.update_of_ne h0]

end IntegerMultBounds.MathlibTM2.M6.BitNode
