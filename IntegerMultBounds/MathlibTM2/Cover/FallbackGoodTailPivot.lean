module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairWeights

/-! Read an unweighted pivot from the compact diagonal and form its two signed reciprocals. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {P U : Type} {T Q A d b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def tailPivotRead : Fin 7 ↪ Fin 19 := ⟨![1,4,18,14,2,3,5],by decide⟩

def signedTailPivot (b i : ℕ) (bank : Fin 19 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord i (tailPivotRead.trans bank))
    (.seq (reusablePivotInverse b ((Fin.castLEEmb (by decide)).trans bank) (bank 16) (bank 17))
      (bsub (bank 4) (bank 0) (bank 12) (bank 1) (bank 2) (bank 3) (bank 5)))

def tailPivotTime (b w H i : ℕ) : ℕ :=
  let C := 48*H*H+152*H+66
  (8*(i*H)+14*H+22) +
      ((6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C)))+(8*H+8))

theorem signedTailPivot_exec (body : P → Pr P T Q A U) (bank : Fin 19 ↪ Fin T)
    (pivot : Fin d → ZMod M) (i : Fin d) (unit : IsUnit (pivot i)) (hb : b.Prime)
    (H : ℕ) (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (record : S.R (bank 18) = (List.ofFn fun j => binSyms H (pivot j).val).flatten ++ tail)
    (modulus : S.R (bank 4) = binSyms H M) (one : S.R (bank 15) = binSyms H (1 : ZMod M).val)
    (clock : (S.R (bank 16)).length = w)
    (free : ∀ j : Fin 19, (j < 13 ∧ j ≠ 4) ∨ j = 14 ∨ j = 17 → S.R (bank j) = []) :
    let x := Ring.inverse (pivot i)
    ∃ z F n, z.user = v.user ∧ n ≤ tailPivotTime b w H i.val ∧
      Exec body (signedTailPivot b i.val bank) (mk v S) n (mk z F) ∧
      F.R (bank 14) = binSyms H (pivot i).val ∧ F.R (bank 0) = binSyms H x.val ∧
      F.R (bank 12) = binSyms H (-x).val ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ j, j ≠ bank 0 → j ≠ bank 14 → j ≠ bank 12 → F.R j = S.R j := by
  intro x
  let row : Matrix (Fin 1) (Fin d) (ZMod M) := fun _ j => pivot j
  have ports : ∀ j : Fin 7, j = 0 ∨ 4 ≤ j → tailPivotRead j < 13 ∧ tailPivotRead j ≠ 4 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (tailPivotRead.trans bank) row 0 i H v S tail
    (by change S.R (bank 18) = _; simpa [matrixWords,row] using record)
    ((congrArg List.length modulus).trans (length_binSyms ..)) (fun j hj => free _ (.inl (ports j hj)))
  let D := {S with R := Function.update S.R (bank 14) (binSyms H (pivot i).val)}
  change Exec body (readMatrixWord (0*d+i.val) _) _ _ (mk u {S with R := Function.update S.R (bank 14) (binSyms H (pivot i).val ++ S.R (bank 14))}) at read
  simp only [Nat.zero_mul,Nat.zero_add,Fin.val_zero,free 14 (by decide),List.append_nil] at read
  have keep (j : Fin 19) (ne : j ≠ 14) : D.R (bank j) = S.R (bank j) := Function.update_of_ne (bank.injective.ne ne) _ _
  let r : Fin 16 ↪ Fin T := (Fin.castLEEmb (by decide : 16 ≤ 19)).trans bank
  have apart : ∀ j : Fin 16, (Fin.castLEEmb (by decide : 16 ≤ 19)) j ≠ 17 := by decide
  have small : ∀ j : Fin 16, j ≠ 4 → j < 13 →
    let k := (Fin.castLEEmb (by decide : 16 ≤ 19)) j
    k ≠ 14 ∧ k < 13 ∧ k ≠ 4 := by decide
  obtain ⟨y,E,t,hy,ht,invert,_,pos,left,inp,out,frame⟩ := reusablePivotInverse_exec body b w hb _ unit r
    (bank 16) (bank 17) (by simp [r,List.nodup_cons,bank.injective.eq_iff]) (fun j => bank.injective.ne (apart j))
    H hm u D (by rw [keep 16 (by decide),clock]) ((keep 17 (by decide)).trans (free 17 (by decide)))
    (Function.update_self ..) ((keep 15 (by decide)).trans one) ((keep 4 (by decide)).trans modulus)
    (fun j h lo => (keep _ (small j h lo).1).trans (free _ (.inl (small j h lo).2)))
  have saved (j : Fin 19) (h : j ≠ 0) (ne : j ≠ 14) : E.R (bank j) = S.R (bank j) :=
    (frame _ (bank.injective.ne h)).trans (keep j ne)
  have scratch (j : Fin 19) (lo : j ≠ 0) (hi : j < 13) (ne : j ≠ 4) :=
    (saved j lo (by omega)).trans (free _ (.inl ⟨hi,ne⟩))
  obtain ⟨z,hz,_,_,sub⟩ := bsub_exec body (a := bank 4) (b := bank 0) (c := bank 12)
    (tx := bank 1) (ty := bank 2) (tz := bank 3) (cy := bank 5)
    (by simp [List.nodup_cons,bank.injective.eq_iff]) (bank.injective.ne (by decide)) (bank.injective.ne (by decide))
    hm (x.val_lt.trans hm) y E ((saved 4 (by decide) (by decide)).trans modulus) pos
    (scratch 1 (by decide) (by decide) (by decide)) (scratch 2 (by decide) (by decide) (by decide))
    (scratch 3 (by decide) (by decide) (by decide))
  have : Fact (1 < M) := ⟨one_lt_pow₀ hb.one_lt (by omega)⟩
  have ne : x.val ≠ 0 := by
    intro h
    have zero : x = 0 := by simpa using h
    have cancel : pivot i * x = 1 := Ring.mul_inverse_cancel _ unit
    simp [zero] at cancel
  rw [negWordValue x ne hm,scratch 12 (by decide) (by decide) (by decide),List.append_nil] at sub
  refine ⟨z,_,_,hz.trans (hy.trans hu),Nat.add_le_add_left (Nat.add_le_add_right ht _) _,
    Exec.seq read (Exec.seq invert sub),?_,?_,Function.update_self ..,left,inp,out,?_⟩
  · exact (Function.update_of_ne (bank.injective.ne (by decide : (14 : Fin 19) ≠ 12)) _ _).trans
      ((frame _ (bank.injective.ne (by decide : (14 : Fin 19) ≠ 0))).trans (Function.update_self ..))
  · exact (Function.update_of_ne (bank.injective.ne (by decide : (0 : Fin 19) ≠ 12)) _ _).trans pos
  · intro j h0 h14 h12
    exact (Function.update_of_ne h12 _ _).trans ((frame j h0).trans (Function.update_of_ne h14 _ _))

end IntegerMultBounds.MathlibTM2.Cover.Fallback
