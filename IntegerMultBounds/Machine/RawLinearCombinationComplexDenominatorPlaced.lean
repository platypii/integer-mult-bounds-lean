import IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorSequence
import IntegerMultBounds.Machine.CleanSubbank

/-! Fixed polynomial scalar row sequences run at actual selected permanent
source/count/denominator ports. Every local work slot is initially blank and
returns blank, and the arbitrary complementary caller frame is preserved.
Input requirements are literal source words, heads and marked descriptors. -/
namespace IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorPlaced
noncomputable section
open ButterflyStreamData (Coefficient full)
open RadixLinearCombinationRefresh (Expr Size)
open RawLinearCombinationComplexRowSequence (execute)
open RecursiveChildQuotientsConstant (bits)
open RawLinearCombinationComplexDenominatorSequence (bank)
variable {c S n k : ℕ} {ι : Type*}

abbrev arrayCount (c S : ℕ) := RawLinearCombinationComplexCoefficient.count c S
abbrev localCount (c S : ℕ) := RawLinearCombinationComplexDenominatorSequence.count c S

def source (i : Fin c) : Fin (localCount c S) :=
  Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (Fin.castAdd (c+(c+(c+S))) i)))
def countPort : Fin (localCount c S) :=
  Fin.castAdd 1 (Fin.castAdd 2 (Fin.natAdd (arrayCount c S) (0 : Fin 1)))
def livePort : Fin (localCount c S) := RawLinearCombinationComplexDenominatorSequence.live

def ports : Fin (c+2) → Fin (localCount c S) :=
  Fin.addCases source (fun j => if j.val=0 then countPort else livePort)

theorem ports_source (i : Fin c) : ports (S:=S) (Fin.castAdd 2 i)=source i := by simp [ports]
theorem ports_count : ports (c:=c) (S:=S) (Fin.natAdd c (0 : Fin 2))=countPort := by simp [ports]
theorem ports_live : ports (c:=c) (S:=S) (Fin.natAdd c (1 : Fin 2))=livePort := by simp [ports]

private theorem source_val (i : Fin c) : (source (S:=S) i).val=i.val := rfl
private theorem count_val : (countPort (c:=c) (S:=S)).val=arrayCount c S := rfl
private theorem live_val : (livePort (c:=c) (S:=S)).val=arrayCount c S+3 := rfl
private theorem source_lt (i : Fin c) : i.val<arrayCount c S := by
  have := i.isLt
  unfold arrayCount RawLinearCombinationComplexCoefficient.count
  omega

private theorem tail_val (j : Fin 2) :
    (ports (c:=c) (S:=S) (Fin.natAdd c j)).val=
      if j.val=0 then arrayCount c S else arrayCount c S+3 := by
  simp only [ports,Fin.addCases_right]
  split_ifs <;> first | exact count_val | exact live_val

theorem ports_injective : Function.Injective (ports (c:=c) (S:=S)) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      have hv := congrArg Fin.val h
      simp only [ports_source,source_val] at hv
      exact congrArg (Fin.castAdd 2) (Fin.ext hv)
    | right j =>
      have hv := congrArg Fin.val h
      have hi := source_lt (S:=S) i
      fin_cases j <;> simp [ports_source,source_val,tail_val] at hv <;> omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hv := congrArg Fin.val h
      have hj := source_lt (S:=S) j
      fin_cases i <;> simp [ports_source,source_val,tail_val] at hv <;> omega
    | right j =>
      have hv := congrArg Fin.val h
      fin_cases i <;> fin_cases j <;>
        simp [tail_val] at hv <;> rfl

theorem local_source (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) (j : Fin c) :
    (bank (S:=S) data bs d).head (source j)=0 ∧
      (bank (S:=S) data bs d).tape (source j)=full (fun _ => blank) 0 (data j) := by
  simp only [bank,RawLinearCombinationComplexArrayReusable.bank,CountedLoopHeaderClean.bank,
    RawLinearCombinationComplexArrayReusable.normalized,source,Tapes.append,Fin.addCases_left]
  exact ⟨True.intro,True.intro⟩

theorem local_count (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :
    (bank (S:=S) data bs d).head countPort=1 ∧
      (bank (S:=S) data bs d).tape countPort=RadixZeroFill.encodedBinary bs := by
  simp only [bank,RawLinearCombinationComplexArrayReusable.bank,CountedLoopHeaderClean.bank,countPort,
    RawLinearCombinationComplexArrayReusable.originalCount,Tapes.append,Fin.addCases_left,Fin.addCases_right,
    MarkedWordCleanup.one]
  exact ⟨True.intro,True.intro⟩

theorem local_live (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :
    (bank (S:=S) data bs d).head livePort=1 ∧
      (bank (S:=S) data bs d).tape livePort=RadixZeroFill.encodedBinary (bits d) :=
  (RawLinearCombinationComplexDenominatorSequence.bank_live data bs d).symm

private theorem private_blank (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ)
    (i : Fin (localCount c S)) (hi : ¬∃ j,ports j=i) :
    (bank (S:=S) data bs d).head i=0 ∧ (bank (S:=S) data bs d).tape i=(fun _ => blank) := by
  induction i using Fin.addCases (m:=RawLinearCombinationComplexDenominatorSequence.baseCount c S) (n:=1) with
  | right i =>
    have he : i=(0 : Fin 1) := Subsingleton.elim _ _
    subst i
    exact (hi ⟨Fin.natAdd c (1 : Fin 2),ports_live⟩).elim
  | left i =>
    induction i using Fin.addCases (m:=arrayCount c S+1) (n:=2) with
    | right i =>
      simp only [bank,RawLinearCombinationComplexArrayReusable.bank,CountedLoopHeaderClean.bank,
        Tapes.append,Fin.addCases_left,Fin.addCases_right,SharedBank.empty]
      exact ⟨True.intro,True.intro⟩
    | left i =>
      induction i using Fin.addCases (m:=arrayCount c S) (n:=1) with
      | right i =>
        have he : i=(0 : Fin 1) := Subsingleton.elim _ _
        subst i
        exact (hi ⟨Fin.natAdd c (0 : Fin 2),ports_count⟩).elim
      | left i =>
        induction i using Fin.addCases (m:=c) (n:=c+(c+(c+S))) with
        | left i => exact (hi ⟨Fin.castAdd 2 i,ports_source i⟩).elim
        | right i =>
          simp only [bank,RawLinearCombinationComplexArrayReusable.bank,CountedLoopHeaderClean.bank,
            RawLinearCombinationComplexArrayReusable.normalized,RawLinearCombinationCleanup.empty_append]
          simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,RadixLinearCombinationBootstrap.empty]
          exact ⟨True.intro,True.intro⟩


/-- Blank arithmetic controls, output streams, expression storage and loop
work follow from the proved normalized bank; callers supply no cleanliness oracle. -/
theorem strip_blank (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :
    SharedBank.strip (bank (S:=S) data bs d) ports=SharedBank.empty (localCount c S) 2 := by
  apply Placement.Tapes.ext'
  all_goals
    intro i
    by_cases hi : ∃ j,ports (c:=c) (S:=S) j=i
    · simp only [SharedBank.strip,hi,ite_true,SharedBank.empty]
    · have h := private_blank data bs d i hi
      first
        | simpa only [SharedBank.strip,hi,ite_false,SharedBank.empty] using h.1
        | simpa only [SharedBank.strip,hi,ite_false,SharedBank.empty] using h.2

/-- Literal specification of the selected permanent source/count/denominator
ports. The complete caller frame can contain arbitrary data and heads. -/
def Ready (common : Fin (c+2) → Fin k) (v : Tapes k 2)
    (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) : Prop :=
  (∀ j,v.head (common (Fin.castAdd 2 j))=0 ∧
    v.tape (common (Fin.castAdd 2 j))=full (fun _ => blank) 0 (data j)) ∧
  (v.head (common (Fin.natAdd c (0 : Fin 2)))=1 ∧
    v.tape (common (Fin.natAdd c (0 : Fin 2)))=RadixZeroFill.encodedBinary bs) ∧
  (v.head (common (Fin.natAdd c (1 : Fin 2)))=1 ∧
    v.tape (common (Fin.natAdd c (1 : Fin 2)))=RadixZeroFill.encodedBinary (bits d))

private theorem ready_payload (common : Fin (c+2) → Fin k) (v : Tapes k 2)
    (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) (h : Ready common v data bs d) :
    SharedBank.payload (bank (S:=S) data bs d) ports=SharedBank.payload v common := by
  apply Placement.Tapes.ext'
  all_goals
    intro j
    induction j using Fin.addCases with
    | left j =>
      have hl := local_source (S:=S) data bs d j
      first
        | simpa only [SharedBank.payload,ports_source] using hl.1.trans (h.1 j).1.symm
        | simpa only [SharedBank.payload,ports_source] using hl.2.trans (h.1 j).2.symm
    | right j =>
      fin_cases j
      · have hl := local_count (S:=S) data bs d
        first
          | simpa [SharedBank.payload,ports] using hl.1.trans h.2.1.1.symm
          | simpa [SharedBank.payload,ports] using hl.2.trans h.2.1.2.symm
      · have hl := local_live (S:=S) data bs d
        first
          | simpa [SharedBank.payload,ports] using hl.1.trans h.2.2.1.symm
          | simpa [SharedBank.payload,ports] using hl.2.trans h.2.2.2.symm

def installed (common : Fin (c+2) → Fin k) (v : Tapes k 2) (small : Tapes (c+2) 2) : Tapes k 2 :=
  ⟨fun i => if h : ∃ j,common j=i then small.head h.choose else v.head i,
    fun i => if h : ∃ j,common j=i then small.tape h.choose else v.tape i⟩

private theorem installed_payload (common : Fin (c+2) → Fin k) (hc : Function.Injective common)
    (v : Tapes k 2) (small : Tapes (c+2) 2) : SharedBank.payload (installed common v small) common=small := by
  apply Placement.Tapes.ext'
  all_goals
    intro j
    simp only [SharedBank.payload,installed]
    split_ifs with h
    · rw [hc h.choose_spec]
    · exact (h ⟨j,rfl⟩).elim

theorem installed_frame (common : Fin (c+2) → Fin k) (v : Tapes k 2) (small : Tapes (c+2) 2) :
    SharedBank.strip v common=SharedBank.strip (installed common v small) common := by
  apply Placement.Tapes.ext'
  all_goals intro i; by_cases hi : ∃ j,common j=i <;> simp [SharedBank.strip,installed,hi]

def output (common : Fin (c+2) → Fin k) (v : Tapes k 2)
    (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :=
  installed common v (SharedBank.payload (bank (S:=S) data bs d) ports)

/-- Computed permanent endpoints expose the same literal port contract for the
next real stage; only the specified source words and denominator are changed. -/
theorem output_ready (common : Fin (c+2) → Fin k) (hcommon : Function.Injective common)
    (v : Tapes k 2) (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) :
    Ready common (output (S:=S) common v data bs d) data bs d := by
  have hp := installed_payload common hcommon v (SharedBank.payload (bank (S:=S) data bs d) ports)
  have hh (j : Fin (c+2)) := congrFun (congrArg Tapes.head hp) j
  have ht (j : Fin (c+2)) := congrFun (congrArg Tapes.tape hp) j
  refine ⟨?_,?_,?_⟩
  · intro j
    have hs := local_source (S:=S) data bs d j
    constructor
    · exact (hh (Fin.castAdd 2 j)).trans (by simpa only [SharedBank.payload,ports_source] using hs.1)
    · exact (ht (Fin.castAdd 2 j)).trans (by simpa only [SharedBank.payload,ports_source] using hs.2)
  · have hs := local_count (S:=S) data bs d
    constructor
    · exact (hh (Fin.natAdd c (0 : Fin 2))).trans (by simpa only [SharedBank.payload,ports_count] using hs.1)
    · exact (ht (Fin.natAdd c (0 : Fin 2))).trans (by simpa only [SharedBank.payload,ports_count] using hs.2)
  · have hs := local_live (S:=S) data bs d
    constructor
    · exact (hh (Fin.natAdd c (1 : Fin 2))).trans (by simpa only [SharedBank.payload,ports_live] using hs.1)
    · exact (ht (Fin.natAdd c (1 : Fin 2))).trans (by simpa only [SharedBank.payload,ports_live] using hs.2)

theorem output_outside (common : Fin (c+2) → Fin k) (v : Tapes k 2)
    (data : Fin c → Fin n → Coefficient) (bs : List Bool) (d : ℕ) (i : Fin k)
    (hi : ¬∃ j,common j=i) :
    (output (S:=S) common v data bs d).head i=v.head i ∧
      (output (S:=S) common v data bs d).tape i=v.tape i := by
  simp only [output,installed,hi,dite_false,and_self]

def program (hc : 0<c) (es : ι → Fin c → Expr c) (hs : ∀ r j,Size (es r j)≤S)
    (ops : List ι) (common : Fin (c+2) → Fin k) (hcommon : Function.Injective common) :=
  Placement.placed (RawLinearCombinationComplexDenominatorSequence.compile hc es hs ops).2
    (CleanSubbank.placement ports common hcommon)

/-- Actual fixed execution at arbitrary selected permanent source, count and
live denominator ports, with literal inputs and the whole complementary frame
retained. The appended private bank returns completely blank at head zero. -/
theorem runs (hc : 0<c) (es : ι → Fin c → Expr c) (hs : ∀ r j,Size (es r j)≤S)
    (ops : List ι) (common : Fin (c+2) → Fin k) (hcommon : Function.Injective common)
    (v : Tapes k 2) (data : Fin c → Fin n → Coefficient) (w : ℕ)
    (hw : ∀ j i,(data j i).1.length=w ∧ (data j i).2.length=w)
    (bs : List Bool) (hn : Counter.value bs=n) (d : ℕ) (hready : Ready common v data bs d) :
    HoareTime (program hc es hs ops common hcommon)
      (fun z => z=CleanSubbank.bank (s:=localCount c S) v)
      (fun z => z=CleanSubbank.bank (s:=localCount c S)
        (output (S:=S) common v (execute hc es ops data) bs (d+ops.length)))
      (RawLinearCombinationComplexDenominatorSequence.cost es n w bs ops d) := by
  exact CleanSubbank.realizes (RawLinearCombinationComplexDenominatorSequence.compile hc es hs ops).2
    ports common ports_injective hcommon v (output common v (execute hc es ops data) bs (d+ops.length))
    (bank data bs d) (bank (execute hc es ops data) bs (d+ops.length)) _
    (ready_payload common v data bs d hready) (installed_payload common hcommon v _).symm
    (strip_blank data bs d) (strip_blank (execute hc es ops data) bs (d+ops.length))
    (installed_frame common v _)
    (RawLinearCombinationComplexDenominatorSequence.runs hc es hs ops data w hw bs hn d)

end
end IntegerMultBounds.Machine.RawLinearCombinationComplexDenominatorPlaced
