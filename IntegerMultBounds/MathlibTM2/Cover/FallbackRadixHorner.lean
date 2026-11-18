module

public import IntegerMultBounds.MathlibTM2.Host.Auto
public import IntegerMultBounds.MathlibTM2.Host.BinArith
public import IntegerMultBounds.Machine.RadixDigits

/-! A binary scan computes the Horner update for one radix digit at fixed width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node RadixDigits
variable {q : ℕ}

def columnValue (d : Fin q) (b : Bool) := d.val + if b then q else 0

def nextCarry (d : Fin q) (b : Bool) : Fin q :=
  ⟨columnValue d b / 2, by have := d.isLt; cases b <;> simp [columnValue] <;> omega⟩

def radixHorner (d : Fin q) : Auto q 1 1 where
  init := digitSymbol d
  step := fun s col =>
    let carry := (readDigit s).getD d
    let b := symBit (col 0)
    (digitSymbol (nextCarry carry b),fun _ => bitSymbol ((columnValue carry b).testBit 0))

private def columns (H x : ℕ) := (binSyms (A := q) H x).map fun b (_ : Fin 1) => b

private theorem hornerScan (d carry : Fin q) (H x : ℕ) (i : Fin 1) :
    (((radixHorner d).runWord (digitSymbol carry) (columns H x)).map (· i)) =
      binSyms H (q*x+carry.val) := by
  induction H generalizing x carry with
  | zero => rfl
  | succ H ih =>
    simp only [columns,binSyms_eq,binBits_succ,List.map_cons,Auto.runWord,radixHorner,
      readDigit_symbol,Option.getD_some,symBit_bitSymbol]
    have tail := ih (nextCarry carry (x.testBit 0)) (x/2)
    simp only [columns,binSyms_eq,radixHorner] at tail
    rw [tail]
    have split : q*x+carry.val = 2*(q*(x/2))+columnValue carry (x.testBit 0) := by
      have hx := Nat.mod_add_div x 2
      rw [Nat.testBit_zero]
      by_cases h : x%2 = 1
      · simp [columnValue,h]; nlinarith only [congrArg (q * ·) hx,h,congrArg (q * ·) h]
      · have hz : x%2 = 0 := by omega
        simp [columnValue,hz]; nlinarith only [congrArg (q * ·) hx,congrArg (q * ·) hz]
    rw [split]
    congr 1
    · simp [Nat.testBit_zero]
    · simp only [nextCarry]; congr 2; omega

theorem radixHorner_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q q U)
    {ins outs : Fin 1 → Fin T} {st width tmp : Fin T} (layout : AutoLayout ins outs st width tmp)
    (d : Fin q) (H x : ℕ) (pos : 0 < H) (v : HS T Q q U) (S : Stacks T q)
    (hw : (S.R width).length = H) (blank : S.R tmp = []) (input : S.R (ins 0) = binSyms H x) :
    ∃ z n, z.user = v.user ∧ n ≤ 5*H+8 ∧
      Exec body (autoWords ins outs st width tmp (radixHorner d)) (mk v S) n
        (mk z {S with R := autoRegs S.R ins outs (fun _ => binSyms H (q*x+d.val))}) := by
  obtain ⟨z,n,hz,hn,run⟩ := autoWords_exec_words body layout (radixHorner d) pos hw [columns H x]
    (by simp [columns,length_binSyms]) v S rfl blank
    (by intro i; fin_cases i; simpa [Auto.stream,columns,List.map_map,Function.comp_def] using input)
  have result : (radixHorner d).outWords [columns H x] = fun _ => binSyms H (q*x+d.val) := by
    funext i
    simpa only [Auto.outWords,List.flatMap_singleton,ite_true,radixHorner] using hornerScan d d H x i
  exact ⟨z,n,hz,by simpa [Nat.add_assoc] using hn,result ▸ run⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
