module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPaddingRecord
public import IntegerMultBounds.MathlibTM2.Cover.FallbackCollectRecord

/-! Advance the packed matrix queue after collecting a record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A d W b w : ℕ} {P U α : Type} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

/-- Remove the current matrix, including when it is the final record. -/
theorem consumeMatrix_exec {D : ℕ} [NeZero D] (bank : Fin 35 ↪ Fin T) (body : P → Pr P T Q A U)
    (v : HS T Q A U) (S : Stacks T A) (H : ℕ) (m : Matrix (Fin d) (Fin d) (ZMod D))
    (tail : List (Fin (A+4))) (queue : S.R (bank 34) = matrixWords A H m ++ tail)
    (width : (S.R (bank 2)).length = H) (scratch : S.R (bank 0) = []) :
    ∃ z, z.user = v.user ∧ Exec body (dropWords (bank 2) (bank 34) (bank 0) (d*d)) (mk v S)
      (d*d*(4*H+4)+1) (mk z {S with R := Function.update S.R (bank 34) tail}) := by
  obtain ⟨z,hz,run⟩ := dropWords_exec body (bank.injective.ne (by decide : (2 : Fin 35) ≠ 34))
    (bank.injective.ne (by decide : (2 : Fin 35) ≠ 0)) (bank.injective.ne (by decide : (34 : Fin 35) ≠ 0))
    (d*d) H v S width scratch
  rw [queue,← length_matrixWords A H m,List.drop_left] at run
  exact ⟨z,hz,run⟩

/-- Padding consumes one matrix even when its label is singular. -/
theorem advancePadding_exec {D : ℕ} [NeZero D] (bank : Fin 35 ↪ Fin T) (body : P → Pr P T Q A U)
    (pivot count src acc tmp : Fin T) (regs : [pivot,count,src,acc,tmp].Nodup)
    (outside : ∀ i, bank i ≠ pivot ∧ bank i ≠ src ∧ bank i ≠ acc)
    (v : HS T Q A U) (S : Stacks T A) (H : ℕ) (m : Matrix (Fin d) (Fin d) (ZMod D))
    (rows : Fin d → Fin d) (tail word rest schedule : List (Fin (A+4)))
    (matrix : S.R (bank 34) = matrixWords A H m ++ tail) (width : (S.R (bank 2)).length = H)
    (scratch : S.R (bank 0) = [])
    (pivots : S.R pivot = scheduleCode rows ++ orderedScheduleCode (List.finRange d).reverse rows ++ schedule)
    (payload : S.R src = word ++ rest) (counted : (S.R count).length = word.length) (free : S.R tmp = []) :
    let after := Function.update (Function.update (Function.update S.R pivot schedule) src rest) acc
      (word.reverse ++ S.R acc)
    ∃ z n, z.user = v.user ∧ n ≤ 4*d*d+1+(4*word.length+4)+(d*d*(4*H+4)+1) ∧
      Exec body (.seq (paddingRecord d pivot count src acc tmp) (dropWords (bank 2) (bank 34) (bank 0) (d*d)))
        (mk v S) n (mk z {S with R := Function.update after (bank 34) tail}) := by
  intro after
  obtain ⟨u,l,hu,hl,pad⟩ := paddingRecord_exec body pivot count src acc tmp regs rows v S word rest schedule
    pivots payload counted free
  have keep (i : Fin 35) : after (bank i) = S.R (bank i) := by
    simp [after,Function.update_of_ne,(outside i).1,(outside i).2.1,(outside i).2.2]
  obtain ⟨z,hz,advance⟩ := consumeMatrix_exec bank body u {S with R := after} H m tail
    ((keep 34).trans matrix) ((congrArg List.length (keep 2)).trans width) ((keep 0).trans scratch)
  exact ⟨z,_,hz.trans hu,Nat.add_le_add_right hl _,.seq pad advance⟩

theorem nextRecord_exec (bank : Fin 35 ↪ Fin T) (body : P → Pr P T Q A U)
    (v : HS T Q A U) (S : Stacks T A) (H J : ℕ) (m next : Matrix (Fin d) (Fin d) (ZMod M))
    (tail : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (ready : ShearReady bank H J m (matrixWords A H next ++ tail) sym source dest p q word S) :
    let F := {S with R := Function.update S.R (bank 34) (matrixWords A H next ++ tail)}
    ∃ z, z.user = v.user ∧ Exec body (dropWords (bank 2) (bank 34) (bank 0) (d*d)) (mk v S)
      (d*d*(4*H+4)+1) (mk z F) ∧ ShearReady bank H J next tail sym source dest p q word F := by
  intro F
  obtain ⟨z,hz,run⟩ := consumeMatrix_exec bank body v S H m _ ready.archive
    ((congrArg List.length ready.modulus).trans (length_binSyms ..)) (ready.scratch 0 (by decide)).2
  have keep (i : Fin 35) (hi : i ≠ 34) : F.R (bank i) = S.R (bank i) := Function.update_of_ne (bank.injective.ne hi) _ _
  refine ⟨z,hz,run,⟨(keep 2 (by decide)).trans ready.modulus,(keep 27 (by decide)).trans ready.width,
    (keep 28 (by decide)).trans ready.one,(keep 32 (by decide)).trans ready.padded,
    (congrArg List.length (keep 33 (by decide))).trans ready.clock,Function.update_self ..,?_,?_,?_⟩⟩
  · intro i hi
    exact ⟨(ready.scratch i hi).1,(keep i (fun e => (by decide : (34 : Fin 35) ∉ shearWork) (e ▸ hi))).trans (ready.scratch i hi).2⟩
  · rw [keep 24 (by decide)]
    exact ready.src
  · rw [keep 25 (by decide)]
    exact ready.dst

end IntegerMultBounds.MathlibTM2.Cover.Fallback
