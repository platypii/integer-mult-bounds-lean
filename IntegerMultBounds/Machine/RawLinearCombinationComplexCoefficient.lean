import IntegerMultBounds.Machine.RadixComplexReadBank
import IntegerMultBounds.Machine.RadixControlCleanupBank
import IntegerMultBounds.Machine.RawLinearCombinationComplexFamily

/-! A fixed Gaussian coefficient kernel reads genuine retained source records,
executes every literal wire expression, emits each output record, and erases
both copied component banks. Source symbols and arithmetic workspace are
restored; source and output heads advance by their actual record lengths. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexCoefficient
noncomputable section
open DelimitedRadixRecord (Context)
open RadixLinearCombinationRefresh (Expr Size controls)
open RadixLinearCombinationBootstrap (empty)
variable {c q S : ℕ} [Fact q.Prime]

abbrev count (c S : ℕ) := c+(c+(c+(c+S)))

def sourceBank (ctx : Fin c → Context q) (positions : Fin c → ℤ) : Tapes c q :=
  ⟨positions,fun i => (ctx i).tape⟩

def afterSource (ctx : Fin c → Context q) : Tapes c q :=
  sourceBank ctx (fun i => (ctx i).start+(ctx i).re.length+(ctx i).im.length+2)

def input (ctx : Fin c → Context q) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    Tapes (count c S) q :=
  RadixComplexReadBank.input false ctx (empty c) ((⟨ps,fs⟩ : Tapes c q).append (empty S))

def records (es : Fin c → Expr c) (xs ys : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4))
    (ps : Fin c → ℤ) : Tapes (c+S) q :=
  (⟨fun i => ps i+(RadixLinearCombination.result (es i).erase xs).length+
      (RadixLinearCombination.result (es i).erase ys).length+2,
    fun i => putWord (fs i) (ps i)
      (DelimitedRadixRecord.complex (RadixLinearCombination.result (es i).erase xs)
        (RadixLinearCombination.result (es i).erase ys))⟩ : Tapes c q).append (empty S)

def output (ctx : Fin c → Context q) (es : Fin c → Expr c) (xs ys : ℕ → List (Fin q))
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) : Tapes (count c S) q :=
  (afterSource ctx).append ((empty c).append ((empty c).append (records (S:=S) es xs ys fs ps)))

def readCost (hc : 0<c) (imaginary : Bool) (ctx : Fin c → Context q) : ℕ :=
  RadixComplexReadList.cost imaginary (RadixComplexReadBank.instructions (u:=c+S) imaginary)
    (RadixComplexReadBank.globalContext hc ctx)

def cleanup (hc : 0<c) :=
  seq (RadixControlCleanupBank.program (q:=q) (u:=c+(c+S)) hc)
    (RawLinearCombinationCleanup.prepend (RadixControlCleanupBank.program (q:=q) (u:=c+S) hc) c)

def program (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ i,Size (es i)≤S) :=
  seq (seq (seq (RadixComplexReadBank.program (q:=q) (u:=c+S) hc false)
    (RadixComplexReadBank.program (q:=q) (u:=c+S) hc true))
    (RawLinearCombinationCleanup.prepend (RawLinearCombinationComplexFamily.program hc es hs) c))
    (RawLinearCombinationCleanup.prepend (cleanup (q:=q) (S:=S) hc) c)

def cost (hc : 0<c) (ctx : Fin c → Context q) (es : Fin c → Expr c) (w : ℕ) : ℕ :=
  readCost (S:=S) hc false ctx+readCost (S:=S) hc true ctx+
    2*RawLinearCombinationFieldFamily.cost es (List.finRange c) w+2*c*(2*w+5)+5

omit [Fact q.Prime] in
private theorem read_join (ctx : Fin c → Context q) (xs : ℕ → List (Fin q))
    (hx : ∀ i,(ctx i).re=xs i.val) (tail : Tapes (c+S) q) :
    RadixComplexReadBank.output false ctx xs (empty c) tail=
      RadixComplexReadBank.input true ctx (controls xs) tail := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases with
    | left i => simp [RadixComplexReadBank.output,RadixComplexReadBank.input,RadixComplexReadBank.bank,
        Tapes.append,RadixComplexReadList.start,RadixComplexReadList.field,hx]
    | right i =>
      induction i using Fin.addCases with
      | left i => rfl
      | right i => induction i using Fin.addCases <;> rfl

omit [Fact q.Prime] in
private theorem read_end (ctx : Fin c → Context q) (xs ys : ℕ → List (Fin q))
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    RadixComplexReadBank.output true ctx ys (controls xs) ((⟨ps,fs⟩ : Tapes c q).append (empty S))=
      (afterSource ctx).append (RawLinearCombinationComplexFamily.bank (S:=S) xs ys fs ps) := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [RadixComplexReadBank.output,RadixComplexReadBank.bank,Tapes.append,Fin.addCases_left,
        afterSource,sourceBank,RadixComplexReadList.start,RadixComplexReadList.field,ite_true]
      try omega
    | right i =>
      simp only [RadixComplexReadBank.output,RadixComplexReadBank.bank,Tapes.append,Fin.addCases_right,
        RawLinearCombinationComplexFamily.bank,RawLinearCombinationFieldFamily.bank,ite_true]

private theorem family_end (ctx : Fin c → Context q) (es : Fin c → Expr c)
    (xs ys : ℕ → List (Fin q)) (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    (afterSource ctx).append (RawLinearCombinationComplexFamily.output (S:=S) es xs ys fs ps)=
      (afterSource ctx).append ((controls xs).append ((controls ys).append (records (S:=S) es xs ys fs ps))) := rfl

omit [Fact q.Prime] in
theorem cleanup_runs (hc : 0<c) (xs ys : ℕ → List (Fin q)) (w : ℕ)
    (hx : ∀ j,(xs j).length=w) (hy : ∀ j,(ys j).length=w) (tail : Tapes (c+S) q) :
    HoareTime (cleanup (q:=q) (S:=S) hc)
      (fun v => v=(controls xs).append ((controls ys).append tail))
      (fun v => v=(empty c).append ((empty c).append tail)) (2*c*(2*w+5)+1) := by
  have h0 := RadixControlCleanupBank.runs hc xs w hx ((controls (c:=c) ys).append tail)
  have h1 := RawLinearCombinationCleanup.prepend_runs _ _ _ (empty c)
    (RadixControlCleanupBank.runs hc ys w hy tail)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (le_of_eq (by ring))

/-- Every source field is physically read, every fixed expression is physically
executed, and all private copied controls and arithmetic tapes are blank. -/
theorem runs (hc : 0<c) (ctx : Fin c → Context q) (es : Fin c → Expr c)
    (hs : ∀ i,Size (es i)≤S) (xs ys : ℕ → List (Fin q))
    (hx : ∀ i,(ctx i).re=xs i.val) (hy : ∀ i,(ctx i).im=ys i.val)
    (w : ℕ) (hwx : ∀ j,(xs j).length=w) (hwy : ∀ j,(ys j).length=w)
    (fs : Fin c → ℤ → Fin (q+4)) (ps : Fin c → ℤ) :
    HoareTime (program hc es hs) (fun v => v=input (S:=S) ctx fs ps)
      (fun v => v=output (S:=S) ctx es xs ys fs ps) (cost (S:=S) hc ctx es w) := by
  have h0 := RadixComplexReadBank.runs false hc ctx xs hx (empty c)
    ((⟨ps,fs⟩ : Tapes c q).append (empty S))
  have h1 := RadixComplexReadBank.runs true hc ctx ys hy (controls xs)
    ((⟨ps,fs⟩ : Tapes c q).append (empty S))
  rw [← read_join ctx xs hx,read_end ctx xs ys] at h1
  have h2 := RawLinearCombinationCleanup.prepend_runs _ _ _ (afterSource ctx)
    (RawLinearCombinationComplexFamily.runs hc es hs xs ys w hwx hwy fs ps)
  have h3 := RawLinearCombinationCleanup.prepend_runs _ _ _ (afterSource ctx)
    (cleanup_runs hc xs ys w hwx hwy (records (S:=S) es xs ys fs ps))
  rw [← family_end ctx es xs ys fs ps] at h3
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h)
    (by dsimp only [cost,readCost]; omega)

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexCoefficient
