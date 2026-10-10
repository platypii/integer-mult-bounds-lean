import IntegerMultBounds.Machine.RawLinearCombinationComplexRowSequence
import IntegerMultBounds.Machine.CompactComplexExponentStep

/-! The true common denominator advances once at each completed whole scalar
row. It is stored on a retained marked binary tape, separate from all geometry
and field-width metadata. The coefficient loop never updates this descriptor;
its real in-place increment executes only after copy-back and full cleanup. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorSequence
noncomputable section
open ButterflyStreamData (Coefficient)
open RadixLinearCombinationRefresh (Expr Size)
open RawLinearCombinationComplexArray (result)
open RawLinearCombinationComplexRowSequence (execute rowCost)
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {c S n : ℕ} {ι : Type*}

abbrev baseCount (c S : ℕ) := RawLinearCombinationComplexRowSequence.count c S
abbrev count (c S : ℕ) := baseCount c S+1

def live : Fin (count c S) := Fin.natAdd (baseCount c S) (0 : Fin 1)
def denominator (d : ℕ) : Tapes 1 2 := FiniteReturnStack.bank (BinaryDescriptorStack.descriptor (bits d)) 1

def bank (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :=
  (RawLinearCombinationComplexArrayReusable.bank (S:=S) data bs).append (denominator d)

/-- This is exactly the alphabet-six marked descriptor used by controller
storage7, with its physically normalized descriptor head at one. -/
theorem denominator_format (d : ℕ) :
    (denominator d).tape 0=RadixZeroFill.encodedBinary (bits d) ∧ (denominator d).head 0=1 := by
  constructor
  · exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  · rfl

theorem bank_live (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :
    (bank (S:=S) data bs d).tape live=RadixZeroFill.encodedBinary (bits d) ∧
      (bank (S:=S) data bs d).head live=1 := by
  simpa only [bank,live,Tapes.append,Fin.addCases_right] using denominator_format d

private theorem bank_advance (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :
    setTape (bank (S:=S) data bs d) live (BinaryDescriptorStack.descriptor (bits (d+1))) 1=
      bank (S:=S) data bs (d+1) := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    induction i using Fin.addCases with
    | left i =>
      have hn : Fin.castAdd 1 i≠live (c:=c) (S:=S) := by
        intro h
        have hv := congrArg Fin.val h
        have hi : i.val<baseCount c S := i.isLt
        change i.val=baseCount c S at hv
        omega
      simp only [bank,setTape,Function.update_of_ne hn,Tapes.append,Fin.addCases_left]
    | right i =>
      have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simp only [bank,setTape,live,Function.update_self,Tapes.append,Fin.addCases_right,denominator,FiniteReturnStack.bank]

def incrementProgram := CompactComplexExponentStep.ascendProgram (a:=2) (live (c:=c) (S:=S))

def rowProgram (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S) :=
  seq (extend (RawLinearCombinationComplexArrayReusable.program hc es hs) 1)
    (incrementProgram (c:=c) (S:=S))

/-- The literal row loop, copy-back and private erasure complete before the
single paid physical update of its retained common denominator. -/
theorem row_runs (hc : 0<c) (es : Fin c → Expr c) (hs : ∀ j,Size (es j)≤S)
    (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) (d : ℕ) :
    HoareTime (rowProgram hc es hs) (fun v => v=bank (S:=S) data bs d)
      (fun v => v=bank (S:=S) (result hc es data) bs (d+1)) (rowCost es n w bs+2*(d+2)+1) := by
  have h0 := hoare_extend_eq (RawLinearCombinationComplexArrayReusable.runs hc es hs data w hw bs hn)
    (denominator d)
  have h1 := CompactComplexExponentStep.ascend (live (c:=c) (S:=S))
    (bank (S:=S) (result hc es data) bs d) d
    (by simp only [bank,live,Tapes.append,Fin.addCases_right,denominator,FiniteReturnStack.bank])
    (by simp only [bank,live,Tapes.append,Fin.addCases_right,denominator,FiniteReturnStack.bank])
  rw [bank_advance] at h1
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold rowCost; omega)

def compile (hc : 0<c) (es : ι → Fin c → Expr c) (hs : ∀ r j,Size (es r j)≤S) :
    List ι → Σ states,Program (count c S) states 2
  | [] => ⟨1,skip (count c S) 2 (by unfold count; omega)⟩
  | r::ops => ⟨_,seq (rowProgram hc (es r) (hs r)) (compile hc es hs ops).2⟩

def cost (es : ι → Fin c → Expr c) (n w : ℕ) (bs : List Bool) : List ι → ℕ → ℕ
  | [],_ => 0
  | r::ops,d => rowCost (es r) n w bs+2*(d+2)+2+cost es n w bs ops (d+1)

/-- A fixed literal row sequence physically advances its true denominator
exactly once per whole row. Count, source heads and every generated bank have
exact restored endpoints, including zero coefficient arrays and empty rows. -/
theorem runs (hc : 0<c) (es : ι → Fin c → Expr c) (hs : ∀ r j,Size (es r j)≤S)
    (ops : List ι) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) (d : ℕ) :
    HoareTime (compile hc es hs ops).2 (fun v => v=bank (S:=S) data bs d)
      (fun v => v=bank (S:=S) (execute hc es ops data) bs (d+ops.length)) (cost es n w bs ops d) := by
  induction ops generalizing data d with
  | nil => simpa only [compile,cost,execute,List.length_nil,Nat.add_zero] using skip_hoare (by omega) (bank data bs d)
  | cons r ops ih =>
    have h0 := row_runs hc (es r) (hs r) data w hw bs hn d
    have h1 := ih (result hc (es r) data)
      (RawLinearCombinationComplexArray.result_width hc (es r) data w hw) (d+1)
    have he : d+1+ops.length=d+(r::ops).length := by simp only [List.length_cons]; omega
    rw [he] at h1
    exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by simp only [cost]; omega)

/-- Even an empty coefficient array executes exactly one denominator increment
per literal row, while every source and private stream remains empty. -/
theorem zero_coefficients (hc : 0<c) (es : ι → Fin c → Expr c)
    (hs : ∀ r j,Size (es r j)≤S) (ops : List ι) (data : Fin c → Fin 0 → Coefficient)
    (bs : List Bool) (hn : Counter.value bs=0) (d : ℕ) :
    HoareTime (compile hc es hs ops).2 (fun v => v=bank (S:=S) data bs d)
      (fun v => v=bank (S:=S) data bs (d+ops.length)) (cost es 0 0 bs ops d) := by
  have h := runs hc es hs ops data 0 (by intro j i; exact Fin.elim0 i) bs hn d
  have he : execute hc es ops data=data := by funext j i; exact Fin.elim0 i
  simpa only [he] using h

/-- All exponent scans and joins are included in a uniform finite-row budget. -/
theorem cost_le (es : ι → Fin c → Expr c) (n w : ℕ) (bs : List Bool)
    (ops : List ι) (d B : ℕ) (hB : ∀ r∈ops,rowCost (es r) n w bs≤B) :
    cost es n w bs ops d≤ops.length*(B+2*(d+ops.length+1)+2) := by
  induction ops generalizing d with
  | nil => simp [cost]
  | cons r ops ih =>
    have h0 := hB r List.mem_cons_self
    have h1 := ih (d+1) (fun j hj => hB j (List.mem_cons_of_mem _ hj))
    simp only [cost,List.length_cons] at *
    nlinarith

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorSequence
