import IntegerMultBounds.Machine.RawLinearCombinationComplexArrayReusable

/-! A fixed literal sequence of Gaussian sparse rows executes end to end over
retained polynomial wire streams. Every row reuses the same blank private
bank, so there is no unresolved intermediate head or scratch restoration. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexRowSequence
noncomputable section
open ButterflyStreamData (Coefficient)
open RadixLinearCombinationRefresh (Expr Size)
open RawLinearCombinationComplexArray (result)
open RawLinearCombinationComplexArrayReusable (bank)
variable {c S n : ℕ} {ι : Type*}

abbrev count (c S : ℕ) := (RawLinearCombinationComplexCoefficient.count c S+1)+2

def compile (hc : 0<c) (es : ι → Fin c → Expr c) (hs : ∀ r j,Size (es r j)≤S) :
    List (ι) → Σ states,Program (count c S) states 2
  | [] => ⟨1,skip (count c S) 2 (by unfold count; omega)⟩
  | r::ops => ⟨_,seq (RawLinearCombinationComplexArrayReusable.program hc (es r) (hs r))
      (compile hc es hs ops).2⟩

def execute (hc : 0<c) (es : ι → Fin c → Expr c) :
    List (ι) → (Fin c → Fin n → Coefficient) → (Fin c → Fin n → Coefficient)
  | [],data => data
  | r::ops,data => execute hc es ops (result hc (es r) data)

theorem execute_append (hc : 0<c) (es : ι → Fin c → Expr c)
    (first second : List (ι)) (data : Fin c → Fin n → Coefficient) :
    execute hc es (first++second) data=execute hc es second (execute hc es first data) := by
  induction first generalizing data with
  | nil => rfl
  | cons r ops ih => exact ih (result hc (es r) data)

def rowCost (es : Fin c → Expr c) (n w : ℕ) (bs : List Bool) :=
  n*(RawLinearCombinationComplexArray.bodyCost es w+6)+11*bs.length+35+
    c*(7*(n*(2*(w+1)))+17)+1

def cost (es : ι → Fin c → Expr c) (ops : List (ι)) (n w : ℕ) (bs : List Bool) :=
  (ops.map (fun r => rowCost (es r) n w bs+1)).sum

theorem execute_width (hc : 0<c) (es : ι → Fin c → Expr c) (ops : List (ι))
    (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w) :
    ∀ j i,(execute hc es ops data j i).1.length=w ∧ (execute hc es ops data j i).2.length=w := by
  induction ops generalizing data with
  | nil => exact hw
  | cons r ops ih =>
    exact ih (result hc (es r) data)
      (RawLinearCombinationComplexArray.result_width hc (es r) data w hw)

/-- Each fixed row genuinely reads every coefficient, executes its expressions,
installs every output into the original source stream, and cleans its work. -/
theorem runs (hc : 0<c) (es : ι → Fin c → Expr c) (hs : ∀ r j,Size (es r j)≤S)
    (ops : List (ι)) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) :
    HoareTime (compile hc es hs ops).2 (fun v => v=bank (S:=S) data bs)
      (fun v => v=bank (S:=S) (execute hc es ops data) bs) (cost es ops n w bs) := by
  induction ops generalizing data with
  | nil => exact skip_hoare (by omega) (bank data bs)
  | cons r ops ih =>
    have h0 := RawLinearCombinationComplexArrayReusable.runs hc (es r) (hs r) data w hw bs hn
    have h1 := ih (result hc (es r) data)
      (RawLinearCombinationComplexArray.result_width hc (es r) data w hw)
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h)
      (by simp only [cost,List.map_cons,List.sum_cons,rowCost]; omega)

theorem cost_le (es : ι → Fin c → Expr c) (ops : List (ι)) (n w : ℕ)
    (bs : List Bool) (B : ℕ) (hB : ∀ r∈ops,rowCost (es r) n w bs+1≤B) :
    cost es ops n w bs≤ops.length*B := by
  induction ops with
  | nil => simp [cost]
  | cons r ops ih =>
    have h0 := hB r List.mem_cons_self
    have h1 := ih (fun j hj => hB j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexRowSequence
