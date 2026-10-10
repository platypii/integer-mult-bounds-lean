import IntegerMultBounds.Machine.RawLinearCombinationFieldEmit

/-! Real and imaginary fixed expressions emit one literal Gaussian record.
Both original control banks are retained; both private arithmetic banks end
blank, and the output head advances by the actual two-field record length. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexEmit
noncomputable section
open RadixLinearCombinationRefresh (Expr)
variable {c q : ℕ} [Fact q.Prime]

def placement (k : ℕ) : Fin ((k+1)+k) ≃ Fin (k+(k+1)) where
  toFun := Fin.addCases
    (Fin.addCases (Fin.castAdd (k+1)) (fun i => Fin.natAdd k (Fin.natAdd k i)))
    (fun i => Fin.natAdd k (Fin.castAdd 1 i))
  invFun := Fin.addCases (fun i => Fin.castAdd k (Fin.castAdd 1 i))
    (Fin.addCases (fun i => Fin.natAdd (k+1) i) (fun i => Fin.castAdd k (Fin.natAdd k i)))
  left_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => induction i using Fin.addCases <;> simp
    | right i => simp
  right_inv := by
    intro i
    induction i using Fin.addCases with
    | left i => simp
    | right i => induction i using Fin.addCases <;> simp

abbrev count (e : Expr c) := RawLinearCombination.count e+(RawLinearCombination.count e+1)

def bank (e : Expr c) (xs ys : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :=
  (RawLinearCombination.input e xs).append ((RawLinearCombination.input e ys).append (MarkedWordCleanup.one f p))

def reWord (e : Expr c) (xs : ℕ → List (Fin q)) := RadixLinearCombination.result e.erase xs

def afterReal (e : Expr c) (xs ys : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :=
  bank e xs ys (putWord f p (DelimitedRadixRecord.field (reWord e xs))) (p+(reWord e xs).length+1)

def output (e : Expr c) (xs ys : ℕ → List (Fin q)) (f : ℤ → Fin (q+4)) (p : ℤ) :=
  bank e xs ys (putWord f p (DelimitedRadixRecord.complex (reWord e xs) (reWord e ys)))
    (p+(reWord e xs).length+(reWord e ys).length+2)

def realProgram (e : Expr c) :=
  Placement.placed (RawLinearCombinationFieldEmit.program (q:=q) e) (placement (RawLinearCombination.count e))
def imagProgram (e : Expr c) :=
  RawLinearCombinationCleanup.prepend (RawLinearCombinationFieldEmit.program (q:=q) e) (RawLinearCombination.count e)
def program (e : Expr c) := seq (realProgram (q:=q) e) (imagProgram e)

omit [Fact q.Prime] in
private theorem active (k : ℕ) (x y : Tapes k q) (z : Tapes 1 q) :
    Placement.active (placement k) (x.append (y.append z))=x.append z := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases <;> simp [Placement.active,placement,Tapes.append]

omit [Fact q.Prime] in
private theorem extra (k : ℕ) (x y : Tapes k q) (z : Tapes 1 q) :
    Placement.extra (placement k) (x.append (y.append z))=y := by
  apply Placement.Tapes.ext'
  all_goals intro i; simp [Placement.extra,placement,Tapes.append]

omit [Fact q.Prime] in
private theorem combined (k : ℕ) (x y : Tapes k q) (z : Tapes 1 q) :
    Placement.combine (placement k) (x.append z) y=x.append (y.append z) := by
  simpa only [active,extra] using Placement.view (placement k) (x.append (y.append z))

theorem runs (e : Expr c) (xs ys : ℕ → List (Fin q)) (b : ℕ)
    (hx : ∀ i,(xs i).length=b) (hy : ∀ i,(ys i).length=b)
    (f : ℤ → Fin (q+4)) (p : ℤ) :
    HoareTime (program e) (fun v => v=bank e xs ys f p) (fun v => v=output e xs ys f p)
      (2*RawLinearCombination.cost e b+4*b+15) := by
  have ha : Placement.active (placement (RawLinearCombination.count e)) (bank e xs ys f p)=
      RawLinearCombinationFieldEmit.input e xs f p := active _ _ _ _
  have hreal := Placement.hoare_at (RawLinearCombinationFieldEmit.runs e xs b hx f p)
    (placement (RawLinearCombination.count e)) (bank e xs ys f p) ha
  have h0 : HoareTime (realProgram e) (fun v => v=bank e xs ys f p)
      (fun v => v=afterReal e xs ys f p) (RawLinearCombination.cost e b+2*b+7) := by
    apply hreal.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨small,rfl,rfl⟩
    rw [Placement.replace,bank,extra,RawLinearCombinationFieldEmit.output,
      RawLinearCombinationFieldEmit.input,combined]
    rfl
  have h1 := RawLinearCombinationCleanup.prepend_runs (RawLinearCombinationFieldEmit.program e)
    _ _ (RawLinearCombination.input e xs)
    (RawLinearCombinationFieldEmit.runs e ys b hy
      (putWord f p (DelimitedRadixRecord.field (reWord e xs))) (p+(reWord e xs).length+1))
  have he :
      (RawLinearCombination.input e xs).append
        (RawLinearCombinationFieldEmit.output e ys
          (putWord f p (DelimitedRadixRecord.field (reWord e xs))) (p+(reWord e xs).length+1))=
      output e xs ys f p := by
    unfold RawLinearCombinationFieldEmit.output RawLinearCombinationFieldEmit.input output
    rw [show p+((reWord e xs).length:ℤ)+1=p+(DelimitedRadixRecord.field (reWord e xs)).length by
      simp [DelimitedRadixRecord.field_length]; omega,putWord_append_forward]
    rw [show p+((DelimitedRadixRecord.field (reWord e xs)).length:ℤ)+
        (RadixLinearCombination.result e.erase ys).length+1=
        p+((reWord e xs).length:ℤ)+(reWord e ys).length+2 by
      simp only [DelimitedRadixRecord.field_length,Nat.cast_add,Nat.cast_one,reWord]; omega]
    rfl
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h.trans he) (by omega)

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexEmit
