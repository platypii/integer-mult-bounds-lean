module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady

/-! Load a reciprocal pair directly from the active diagonal archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {P U α : Type} {T Q A d W b w : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

def pairReadPorts : Fin 7 ↪ Fin 35 := (Fin.castLEEmb (by decide : 7 ≤ 8)).trans matrixReadPorts

def pairInversePorts : Fin 16 ↪ Fin 35 := inverseShearPorts.trans (Fin.castLEEmb (by decide))

def loadPairWeights (b : ℕ) (i : Fin d) (bank : Fin 35 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord (i.val*d+i.val) (pairReadPorts.trans bank))
    (reusablePivotInverse b (pairInversePorts.trans bank) (bank 33) (bank 26))

theorem loadPairWeights_exec (body : P → Pr P T Q A U) (i : Fin d) (bank : Fin 35 ↪ Fin T)
    (a : Fin d → ZMod M) (unit : IsUnit (a i)) (hb : b.Prime) (H J : ℕ) (hm : M < 2^H)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (ready : ShearReady bank H J (Matrix.diagonal a) tail sym source dest p q word S) :
    let C := 48*H*H+152*H+66
    ∃ z n, z.user = v.user ∧ n ≤ (8*((i.val*d+i.val)*H)+14*H+22) +
      (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))) ∧
      Exec body (loadPairWeights b i bank) (mk v S) n (mk z {S with R := Function.update (Function.update S.R (bank 31) (binSyms H (a i).val)) (bank 30) (binSyms H (Ring.inverse (a i)).val)}) := by
  intro C
  have readFree : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → pairReadPorts k ∈ shearWork := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (pairReadPorts.trans bank) (Matrix.diagonal a) i i H v S
    tail ready.archive ((congrArg List.length ready.modulus).trans (length_binSyms ..))
    (fun k h => (ready.scratch _ (readFree k h)).2)
  let D := {S with R := Function.update S.R (bank 31) (binSyms H (a i).val)}
  change Exec body _ _ _ (mk u {S with R := Function.update S.R (bank 31) (_ ++ S.R (bank 31))}) at read
  rw [(ready.scratch 31 (by decide)).2,List.append_nil,Matrix.diagonal_apply_eq] at read
  have keep (k : Fin 35) (ne : k ≠ 31) : D.R (bank k) = S.R (bank k) :=
    Function.update_of_ne (bank.injective.ne ne) _ _
  have inverseFree : ∀ k : Fin 16, k ≠ 4 → k < 13 → pairInversePorts k ≠ 31 ∧ pairInversePorts k ∈ shearWork := by decide
  have outside : ∀ k, pairInversePorts k ≠ 26 := by decide
  obtain ⟨z,F,n,hz,hn,invert,_,val,left,input,output,frame⟩ := reusablePivotInverse_exec body b w hb (a i) unit
    (pairInversePorts.trans bank) (bank 33) (bank 26)
    (by simp [List.nodup_cons,bank.injective.eq_iff,Function.Embedding.trans_apply]; decide)
    (fun k => bank.injective.ne (outside k)) H hm u D
    (by rw [keep 33 (by decide),ready.clock]) ((keep 26 (by decide)).trans (ready.scratch 26 (by decide)).2)
    (Function.update_self ..) ((keep 32 (by decide)).trans ready.padded) ((keep 2 (by decide)).trans ready.modulus)
    (fun k hk h => (keep _ (inverseFree k hk h).1).trans (ready.scratch _ (inverseFree k hk h).2).2)
  change F.R (bank 30) = _ at val
  change ∀ j, j ≠ bank 30 → F.R j = D.R j at frame
  have eq : F = {D with R := Function.update D.R (bank 30) (binSyms H (Ring.inverse (a i)).val)} := by
    cases F
    congr
    funext j
    by_cases hit : j = bank 30
    · simpa only [hit,Function.update_self] using val
    · exact (frame j hit).trans (Function.update_of_ne hit _ _).symm
  rw [eq] at invert
  exact ⟨z,_,hz.trans hu,Nat.add_le_add_left hn _,Exec.seq read invert⟩

def loadOnePair (bank : Fin 35 ↪ Fin T) : Pr P T Q A U :=
  .seq (bcopy (bank 32) (bank 31) (bank 4) (bank 5)) (bcopy (bank 32) (bank 30) (bank 4) (bank 5))

omit [NeZero M] in
theorem loadOnePair_exec (body : P → Pr P T Q A U) (bank : Fin 35 ↪ Fin T)
    (H : ℕ) (v : HS T Q A U) (S : Stacks T A) (one : S.R (bank 32) = binSyms H (1 : ZMod M).val)
    (free : ∀ i ∈ shearWork, S.R (bank i) = []) :
    ∃ z, z.user = v.user ∧ Exec body (loadOnePair bank) (mk v S) (2*(6*H+6))
      (mk z {S with R := Function.update (Function.update S.R (bank 31) (binSyms H (1 : ZMod M).val)) (bank 30) (binSyms H (1 : ZMod M).val)}) := by
  obtain ⟨u,hu,copy⟩ := bcopy_exec body (a := bank 32) (c := bank 31) (t₁ := bank 4) (t₂ := bank 5)
    (by simp [List.nodup_cons,bank.injective.eq_iff]) v S (free 4 (by decide)) (free 5 (by decide))
  rw [one,length_binSyms,free 31 (by decide),List.append_nil] at copy
  let D := {S with R := Function.update S.R (bank 31) (binSyms H (1 : ZMod M).val)}
  have keep (j : Fin 35) (hj : j ≠ 31) : D.R (bank j) = S.R (bank j) := Function.update_of_ne (bank.injective.ne hj) _ _
  obtain ⟨z,hz,again⟩ := bcopy_exec body (a := bank 32) (c := bank 30) (t₁ := bank 4) (t₂ := bank 5)
    (by simp [List.nodup_cons,bank.injective.eq_iff]) u D ((keep 4 (by decide)).trans (free 4 (by decide)))
      ((keep 5 (by decide)).trans (free 5 (by decide)))
  rw [keep 32 (by decide),one,length_binSyms,keep 30 (by decide),free 30 (by decide),List.append_nil] at again
  exact ⟨z,hz.trans hu,by rw [two_mul]; exact Exec.seq copy again⟩

/-- For a nonzero residue the representative of its negative is the modulus
minus its representative. Both operands already have the same tape width. -/
def loadSignedPairWeights (b : ℕ) (i : Fin d) (bank : Fin 35 ↪ Fin T) (useOne : Bool := false) : Pr P T Q A U :=
  .seq (if useOne then loadOnePair bank else loadPairWeights b i bank) (bsub (bank 2) (bank 30) (bank 29) (bank 4) (bank 5) (bank 6) (bank 7))

theorem loadSignedPairWeights_exec (body : P → Pr P T Q A U) (i : Fin d) (bank : Fin 35 ↪ Fin T)
    (a : Fin d → ZMod M) (unit : IsUnit (a i)) (hb : b.Prime) (H J : ℕ) (hm : M < 2^H)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))) (sym : α → Fin 4)
    (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (ready : ShearReady bank H J (Matrix.diagonal a) tail sym source dest p q word S) (useOne : Bool := false) :
    let C := 48*H*H+152*H+66
    let weight := if useOne then 1 else a i
    let inv := Ring.inverse weight
    let loaded := Function.update (Function.update S.R (bank 31) (binSyms H weight.val)) (bank 30) (binSyms H inv.val)
    ∃ z n, z.user = v.user ∧ n ≤ (8*((i.val*d+i.val)*H)+14*H+22) +
      (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))) + (8*H+8) ∧
      Exec body (loadSignedPairWeights b i bank useOne) (mk v S) n
        (mk z {S with R := Function.update loaded (bank 29) (binSyms H (-inv).val)}) := by
  intro C weight inv loaded
  have loadRun : ∃ u l, u.user = v.user ∧ l ≤ (8*((i.val*d+i.val)*H)+14*H+22) +
      (6*w+6+(14*H+16+(b-2)*C+C+w*(12*H+15+b*C))) ∧
      Exec body (if useOne then loadOnePair bank else loadPairWeights b i bank) (mk v S) l (mk u {S with R := loaded}) := by
    cases useOne
    · exact loadPairWeights_exec body i bank a unit hb H J hm v S tail sym source dest p q word ready
    · obtain ⟨u,hu,run⟩ := loadOnePair_exec body bank H v S ready.padded (fun j hj => (ready.scratch j hj).2)
      exact ⟨u,2*(6*H+6),hu,by omega,by simpa [loaded,inv,weight] using run⟩
  obtain ⟨u,l,hu,hl,load⟩ := loadRun
  have unitWeight : IsUnit weight := by cases useOne <;> simp_all [weight]
  let D := {S with R := loaded}
  have keep (j : Fin 35) (h : j ≠ 30) (h' : j ≠ 31) : D.R (bank j) = S.R (bank j) :=
    (Function.update_of_ne (bank.injective.ne h) _ _).trans (Function.update_of_ne (bank.injective.ne h') _ _)
  have free (j : Fin 35) (h : j ≠ 30) (h' : j ≠ 31) (hj : j ∈ shearWork) := (keep j h h').trans (ready.scratch j hj).2
  obtain ⟨z,hz,_,_,sub⟩ := bsub_exec body (a := bank 2) (b := bank 30) (c := bank 29)
    (tx := bank 4) (ty := bank 5) (tz := bank 6) (cy := bank 7)
    (by simp [List.nodup_cons,bank.injective.eq_iff]) (bank.injective.ne (by decide)) (bank.injective.ne (by decide))
    hm (inv.val_lt.trans hm) u D ((keep 2 (by decide) (by decide)).trans ready.modulus) (Function.update_self ..)
    (free 4 (by decide) (by decide) (by decide)) (free 5 (by decide) (by decide) (by decide))
    (free 6 (by decide) (by decide) (by decide))
  have : Fact (1 < M) := ⟨one_lt_pow₀ hb.one_lt (by omega)⟩
  have ne : inv.val ≠ 0 := fun eq => (Ring.isUnit_iff_inverse_ne_zero.mp unitWeight) (by apply ZMod.val_injective; simpa using eq)
  have bound := inv.val_lt
  have neg : (M+2^H-inv.val)%2^H = (-inv).val := by
    rw [ZMod.neg_val',Nat.mod_eq_of_lt (show M-inv.val < M by omega),
      show M+2^H-inv.val = M-inv.val+2^H by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  rw [neg,free 29 (by decide) (by decide) (by decide),List.append_nil] at sub
  exact ⟨z,_,hz.trans hu,Nat.add_le_add_right hl _,Exec.seq load sub⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
