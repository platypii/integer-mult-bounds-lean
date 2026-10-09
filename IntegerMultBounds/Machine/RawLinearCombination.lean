import IntegerMultBounds.Machine.RawLinearCombinationCleanup

/-! Exact shared-input radix linear arithmetic from blank private storage.
Repeated expression sources are physically copied; every private copy is
cleared afterward. Runtime is measured in word length, not represented value. -/
namespace IntegerMultBounds.Machine.RawLinearCombination
noncomputable section
open RadixLinearCombinationRefresh (Expr Size controls)
open RawLinearCombinationCleanup (prepend prepend_runs)
variable {c q : ℕ} [Fact q.Prime]

abbrev count (e : Expr c) := c+Size e

def input (e : Expr c) (xs : ℕ → List (Fin q)) : Tapes (count e) q :=
  (controls xs).append (RadixLinearCombinationBootstrap.empty (Size e))
def output (e : Expr c) (xs : ℕ → List (Fin q)) : Tapes (count e) q :=
  (controls xs).append (RawLinearCombinationCleanup.clean e (RadixLinearCombination.result e.erase xs))

def initializer (e : Expr c) := prepend (RadixLinearCombinationBootstrap.initProgram (q:=q) e) c
def arithmetic (e : Expr c) := prepend (RadixLinearCombination.program (q:=q) e.erase) c
def cleanup (e : Expr c) := prepend (RawLinearCombinationCleanup.program (q:=q) e) c

def program (e : Expr c) :=
  seq (seq (seq (initializer (q:=q) e) (RadixLinearCombinationRefresh.program e)) (arithmetic e)) (cleanup e)

def refreshCost : Expr c → ℕ → ℕ
  | .term _ _,b => 2*b+8
  | .add l r,b => refreshCost l b+refreshCost r b+1

def cost (e : Expr c) (b : ℕ) := RadixLinearCombinationBootstrap.initCost e+refreshCost e b+
  RadixLinearCombination.runtime e.erase b+RawLinearCombinationCleanup.cost e b+3

omit [Fact q.Prime] in
theorem refresh_cost (e : Expr c) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i,(xs i).length=b) :
    RadixLinearCombinationRefresh.runtime e xs (fun _ => [])=refreshCost e b := by
  induction e with
  | term i r => simp [RadixLinearCombinationRefresh.runtime,refreshCost,hw]
  | add l r hl hr => simp only [RadixLinearCombinationRefresh.runtime,refreshCost,hl,hr]

theorem runs (e : Expr c) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i,(xs i).length=b) :
    HoareTime (program e) (fun v => v=input e xs) (fun v => v=output e xs) (cost e b) := by
  have hi := prepend_runs (RadixLinearCombinationBootstrap.initProgram e) _ _ (controls (c:=c) xs)
    (RadixLinearCombinationBootstrap.init_hoare e)
  have hr := RadixLinearCombinationRefresh.refresh_hoare e xs (fun _ => [])
  rw [refresh_cost e xs b hw] at hr
  have ha := prepend_runs (RadixLinearCombination.program e.erase) _ _ (controls (c:=c) xs)
    (RadixLinearCombination.compute_hoare e.erase xs b hw)
  have hc := prepend_runs (RawLinearCombinationCleanup.program e) _ _ (controls (c:=c) xs)
    (RawLinearCombinationCleanup.runs e xs (RadixLinearCombination.result e.erase xs) b hw)
  exact (((hi.seq hr).seq ha).seq hc).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

/-- Output retains precisely the original radix width. -/
theorem result_length (e : Expr c) (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i,(xs i).length=b) :
    (RadixLinearCombination.result e.erase xs).length=b := RadixLinearCombination.result_length _ _ _ hw

/-- Arithmetic validity is a finite coefficient check, separate from runtime. -/
theorem result_value (e : Expr c) (he : RadixLinearCombination.Valid (q:=q) e.erase)
    (xs : ℕ → List (Fin q)) (b : ℕ) (hw : ∀ i,(xs i).length=b) :
    (RadixDigits.value (RadixLinearCombination.result e.erase xs) : ZMod (q^b))=
      RadixLinearCombination.valueMod b e.erase xs := RadixLinearCombination.result_value _ he _ _ hw

/-- Syntax determines the exact affine cost in radix-word width. -/
theorem cost_affine (e : Expr c) (b : ℕ) :
    cost e b+(6*b+21)=RadixLinearCombinationRefresh.leaves e*(12*b+42) := by
  induction e with
  | term i r => simp [cost,RadixLinearCombinationBootstrap.initCost,refreshCost,
      RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.runtime,
      RawLinearCombinationCleanup.cost,RadixLinearCombinationRefresh.leaves]; omega
  | add l r hl hr =>
    have hc : cost (.add l r) b=cost l b+cost r b+6*b+21 := by
      simp only [cost,RadixLinearCombinationBootstrap.initCost,refreshCost,
        RadixLinearCombinationRefresh.Expr.erase,RadixLinearCombination.runtime,
        RawLinearCombinationCleanup.cost]
      omega
    rw [hc,RadixLinearCombinationRefresh.leaves,add_mul]
    omega

theorem cost_le (e : Expr c) (b : ℕ) :
    cost e b ≤ RadixLinearCombinationRefresh.leaves e*(12*b+42) := by
  have := cost_affine e b
  omega

end
end IntegerMultBounds.Machine.RawLinearCombination
