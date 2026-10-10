import IntegerMultBounds.Machine.RawLinearCombinationComplexCoefficient
import IntegerMultBounds.Machine.ButterflyStreamEndpoint
import IntegerMultBounds.Machine.CountedLoopHeaderClean

/-! A fixed runtime-counted scalar stream executes the actual expression family
on every coefficient of every retained wire polynomial. The source contexts
are derived from the literal arrays; all coefficient and loop work is blank. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexArray
noncomputable section
open ButterflyStreamData (Coefficient full prefixTape position)
open RadixLinearCombinationRefresh (Expr Size)
open RadixLinearCombinationBootstrap (empty)
variable {c S n : ℕ}

def index (hc : 0<c) (j : ℕ) : Fin c := ⟨j%c,Nat.mod_lt _ hc⟩
def real (hc : 0<c) (data : Fin c → Fin n → Coefficient) (i : Fin n) (j : ℕ) :=
  (data (index hc j) i).1
def imag (hc : 0<c) (data : Fin c → Fin n → Coefficient) (i : Fin n) (j : ℕ) :=
  (data (index hc j) i).2

theorem index_val (hc : 0<c) (j : Fin c) : index hc j.val=j := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt j.isLt

def result (hc : 0<c) (es : Fin c → Expr c) (data : Fin c → Fin n → Coefficient)
    (j : Fin c) (i : Fin n) : Coefficient :=
  (RadixLinearCombination.result (es j).erase (real hc data i),
    RadixLinearCombination.result (es j).erase (imag hc data i))

def contexts (f : Fin c → ℤ → Fin 6) (p : Fin c → ℤ)
    (data : Fin c → Fin n → Coefficient) (i : Fin n) :=
  fun j => ButterflyStreamData.context (f j) (p j) (data j) i

def state (hc : 0<c) (es : Fin c → Expr c) (f g : Fin c → ℤ → Fin 6)
    (p r : Fin c → ℤ) (data : Fin c → Fin n → Coefficient) (k : ℕ) :
    Tapes (RawLinearCombinationComplexCoefficient.count c S) 2 :=
  (⟨fun j => position (p j) (data j) k,fun j => full (f j) (p j) (data j)⟩ : Tapes c 2).append
    ((empty c).append ((empty c).append
      ((⟨fun j => position (r j) (result hc es data j) k,
        fun j => prefixTape (g j) (r j) (result hc es data j) k⟩ : Tapes c 2).append (empty S))))

def outputs (hc : 0<c) (es : Fin c → Expr c) (g : Fin c → ℤ → Fin 6)
    (r : Fin c → ℤ) (data : Fin c → Fin n → Coefficient) (k : ℕ) :=
  fun j => prefixTape (g j) (r j) (result hc es data j) k

def outputPositions (hc : 0<c) (es : Fin c → Expr c) (r : Fin c → ℤ)
    (data : Fin c → Fin n → Coefficient) (k : ℕ) :=
  fun j => position (r j) (result hc es data j) k

theorem coefficient_input (hc : 0<c) (es : Fin c → Expr c) (f g : Fin c → ℤ → Fin 6)
    (p r : Fin c → ℤ) (data : Fin c → Fin n → Coefficient) (i : Fin n) :
    RawLinearCombinationComplexCoefficient.input (S:=S) (contexts f p data i)
      (outputs hc es g r data i.val) (outputPositions hc es r data i.val)=
      state hc es f g p r data i.val := by
  simp only [RawLinearCombinationComplexCoefficient.input,RadixComplexReadBank.input,
    RadixComplexReadBank.bank,RadixComplexReadList.start,Bool.false_eq_true,ite_false,
    contexts,ButterflyStreamData.context_tape,ButterflyStreamData.context_start,
    state]
  rfl

theorem coefficient_output (hc : 0<c) (es : Fin c → Expr c) (f g : Fin c → ℤ → Fin 6)
    (p r : Fin c → ℤ) (data : Fin c → Fin n → Coefficient) (i : Fin n) :
    RawLinearCombinationComplexCoefficient.output (S:=S) (contexts f p data i) es
      (real hc data i) (imag hc data i) (outputs hc es g r data i.val)
      (outputPositions hc es r data i.val)=state hc es f g p r data (i.val+1) := by
  apply Placement.Tapes.ext'
  all_goals
    intro j
    induction j using Fin.addCases with
    | left j =>
      simp only [RawLinearCombinationComplexCoefficient.output,RawLinearCombinationComplexCoefficient.afterSource,
        RawLinearCombinationComplexCoefficient.sourceBank,Tapes.append,Fin.addCases_left,contexts,state]
      first
        | rw [ButterflyStreamData.context_start]
          exact (ButterflyStreamData.position_succ (p j) (data j) i).symm
        | exact ButterflyStreamData.context_tape _ _ _ _
    | right j =>
      induction j using Fin.addCases with
      | left j => simp only [RawLinearCombinationComplexCoefficient.output,state,Tapes.append,Fin.addCases_right,Fin.addCases_left]
      | right j =>
        induction j using Fin.addCases with
        | left j => simp only [RawLinearCombinationComplexCoefficient.output,state,Tapes.append,Fin.addCases_right,Fin.addCases_left]
        | right j =>
          induction j using Fin.addCases with
          | left j =>
            simp only [RawLinearCombinationComplexCoefficient.output,RawLinearCombinationComplexCoefficient.records,
              Tapes.append,Fin.addCases_right,Fin.addCases_left,state]
            first
              | exact (ButterflyStreamData.position_succ (r j) (result hc es data j) i).symm
              | exact ButterflyStreamData.prefixTape_succ (g j) (r j) (result hc es data j) i
          | right j => simp only [RawLinearCombinationComplexCoefficient.output,RawLinearCombinationComplexCoefficient.records,
              state,Tapes.append,Fin.addCases_right]

theorem real_width (hc : 0<c) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) (i : Fin n) :
    ∀ j,(real hc data i j).length=w := fun j => (hw (index hc j) i).1

theorem imag_width (hc : 0<c) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) (i : Fin n) :
    ∀ j,(imag hc data i j).length=w := fun j => (hw (index hc j) i).2

theorem result_width (hc : 0<c) (es : Fin c → Expr c) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) (j : Fin c) (i : Fin n) :
    (result hc es data j i).1.length=w ∧ (result hc es data j i).2.length=w :=
  ⟨RawLinearCombination.result_length _ _ w (real_width hc data w hw i),
    RawLinearCombination.result_length _ _ w (imag_width hc data w hw i)⟩

theorem read_cost (hc : 0<c) (imaginary : Bool) (ctx : Fin c → DelimitedRadixRecord.Context 2)
    (w : ℕ) (hw : ∀ j,(RadixComplexReadList.field imaginary (ctx j)).length=w) :
    RawLinearCombinationComplexCoefficient.readCost (S:=S) hc imaginary ctx=c*(2*w+7) := by
  rw [RawLinearCombinationComplexCoefficient.readCost,RadixComplexReadList.cost,
    RadixComplexReadBank.instructions,List.map_ofFn]
  simp only [Function.comp_def,RadixComplexReadBank.instruction,RadixComplexReadBank.context_source,hw]
  simp

def bodyCost (es : Fin c → Expr c) (w : ℕ) :=
  2*c*(2*w+7)+2*RawLinearCombinationFieldFamily.cost es (List.finRange c) w+2*c*(2*w+5)+5

theorem coefficient_cost (hc : 0<c) (es : Fin c → Expr c)
    (ctx : Fin c → DelimitedRadixRecord.Context 2) (w : ℕ)
    (hw : ∀ j,(ctx j).re.length=w ∧ (ctx j).im.length=w) :
    RawLinearCombinationComplexCoefficient.cost (S:=S) hc ctx es w=bodyCost es w := by
  simp only [RawLinearCombinationComplexCoefficient.cost,
    read_cost hc false ctx w (fun j => (hw j).1),read_cost hc true ctx w (fun j => (hw j).2),bodyCost]
  ring

def body (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S) :=
  extend (RawLinearCombinationComplexCoefficient.program (q:=2) hc es hs) 1

def program (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S) :=
  CountedLoopHeaderClean.program (body hc es hs)
    (Fin.natAdd (RawLinearCombinationComplexCoefficient.count c S) (0 : Fin 1))

def counted (hc : 0<c) (es : Fin c → Expr c) (f g : Fin c → ℤ → Fin 6)
    (p r : Fin c → ℤ) (data : Fin c → Fin n → Coefficient) (bs : List Bool) (k : ℕ) :=
  (state (S:=S) hc es f g p r data k).append
    (MarkedWordCleanup.one (RadixZeroFill.encodedBinary bs) 1)

/-- The same finite coefficient kernel handles every literal polynomial entry.
The original count header is retained and both loop control tapes are erased. -/
theorem runs (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S)
    (f g : Fin c → ℤ → Fin 6) (p r : Fin c → ℤ) (data : Fin c → Fin n → Coefficient)
    (w : ℕ) (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) :
    HoareTime (program hc es hs)
      (fun v => v=CountedLoopHeaderClean.bank (counted (S:=S) hc es f g p r data bs 0))
      (fun v => v=CountedLoopHeaderClean.bank (counted (S:=S) hc es f g p r data bs n))
      (n*(bodyCost es w+6)+11*bs.length+35) := by
  have hb : ∀ i<n,HoareTime (body hc es hs)
      (fun v => v=counted hc es f g p r data bs i)
      (fun v => v=counted hc es f g p r data bs (i+1)) (bodyCost es w) := by
    intro i hi
    let ii : Fin n := ⟨i,hi⟩
    have h := RawLinearCombinationComplexCoefficient.runs hc (contexts f p data ii) es hs
      (real hc data ii) (imag hc data ii)
      (by intro j; simp [contexts,ButterflyStreamData.context,real,index_val])
      (by intro j; simp [contexts,ButterflyStreamData.context,imag,index_val])
      w (real_width hc data w hw ii) (imag_width hc data w hw ii)
      (outputs hc es g r data i) (outputPositions hc es r data i)
    rw [coefficient_input,coefficient_output,coefficient_cost hc es _ w (fun j => hw j ii)] at h
    exact hoare_extend_eq h (MarkedWordCleanup.one (RadixZeroFill.encodedBinary bs) 1)
  have h := CountedLoopHeaderClean.runs (body hc es hs)
    (Fin.natAdd (RawLinearCombinationComplexCoefficient.count c S) (0 : Fin 1)) bs n
    (counted hc es f g p r data bs) (fun _ => bodyCost es w) (by simp [counted,Tapes.append,MarkedWordCleanup.one]) hn hb
  exact h.consequence (fun _ h => h) (fun _ h => h) (by
    simp only [CountedLoopHeaderClean.cost,Finset.sum_const,Finset.card_range,smul_eq_mul]
    exact le_of_eq (by ring))

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexArray
