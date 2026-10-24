module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryZeroField
public import IntegerMultBounds.MathlibTM2.Routing.LowPadNumeral

/-! Generate the inner repair record count `2^n` from binary dimension, using
one high bit and the existing dynamic zero-field primitive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def repairRecordCountSlot : BinaryZeroReg → Fin 6
  | .width => 0
  | .dst => 1
  | .unary => 2
  | .scratch i => ⟨3+i.val,by have := i.isLt; omega⟩

theorem repairRecordCountSlot_injective : Function.Injective repairRecordCountSlot := by
  intro a b h
  cases a <;> cases b
  all_goals first | rfl | skip
  all_goals
    have hv := congrArg (fun i : Fin 6 => i.val) h
    simp [repairRecordCountSlot] at hv <;> first | omega | (congr 1; apply Fin.ext; omega)

def repairRecordCountGenerateProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (.act (Action.push (.rt (rg 1)) (fun _ => bitSymbol true) .done))
    (binaryZeroFieldProgram (rg ∘ repairRecordCountSlot))

theorem repairRecordCountGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L n : ℕ) (hn : n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ i : Fin 6, i ≠ 0 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (4 * n + 11) + 8 * n + 13 ∧
      Exec body (repairRecordCountGenerateProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 1) (binSyms (n+1) (2 ^ n)) }) := by
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) [bitSymbol true] }
  have hp : (Action.push (.rt (rg 1)) (fun _ => bitSymbol true) .done : Act T Q A U).run (mk v S) = mk v C := by
    simp [Action.run,update_rt,C,hblank 1 (by decide)]
  obtain ⟨v',m,hu,hm,he⟩ := binaryZeroField_exec body (rg ∘ repairRecordCountSlot)
    (hrg.comp repairRecordCountSlot_injective) L n hn v C
    (by simpa [C,repairRecordCountSlot,hrg.eq_iff] using hsrc)
    (by simp [C,repairRecordCountSlot,hrg.eq_iff,hblank 2 (by decide)]) (by
      intro i
      fin_cases i <;> simp [C,repairRecordCountSlot,hrg.eq_iff,
        hblank 3 (by decide),hblank 4 (by decide),hblank 5 (by decide)])
  have hd : C.R ((rg ∘ repairRecordCountSlot) .dst) = [bitSymbol true] := by simp [C,repairRecordCountSlot]
  have hw : (binSyms n 0 ++ [bitSymbol true] : List (Fin (A+4))) = binSyms (n+1) (2 ^ n) := by
    change binSyms n 0 ++ binSyms 1 1 = binSyms (n+1) (2 ^ n)
    simpa only [Nat.mul_one] using (binSyms_lowPad (A := A) n 1 1 (by decide))
  rw [hd,hw] at he
  have hf : ({ C with R := Function.update C.R (rg 1) (binSyms (n+1) (2 ^ n)) } : Stacks T A) =
      { S with R := Function.update S.R (rg 1) (binSyms (n+1) (2 ^ n)) } := by simp [C]
  change Exec body _ (mk v C) m (mk v' { C with R := Function.update C.R (rg 1) (binSyms (n+1) (2 ^ n)) }) at he
  rw [hf] at he
  exact ⟨v',1+m,hu,by omega,Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) he⟩

end IntegerMultBounds.MathlibTM2.Routing
