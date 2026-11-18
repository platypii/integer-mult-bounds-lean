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

end IntegerMultBounds.MathlibTM2.Cover.Fallback
