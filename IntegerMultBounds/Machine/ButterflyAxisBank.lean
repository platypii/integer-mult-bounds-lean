import IntegerMultBounds.Machine.ButterflyAxisRouting
import IntegerMultBounds.Machine.RecursiveRowsRoleBank

/-! One permanent bank shared by selected-bit split, paid paired arithmetic,
and merge. The common source is slot 56; paired inputs are slots 0/1 and outputs
2/3. Original count/length and six shape headers remain retained throughout. -/
namespace IntegerMultBounds.Machine.ButterflyAxisBank
noncomputable section
open ButterflyStreamData
open RecursiveInterchangeLayout (Descriptor)
open RecursiveInterchangeRows (groups)
variable {v : Descriptor} {N : ℕ}

abbrev LocalTapes := RecursiveRowsRoleBank.LocalTapes 2

def data (ss : Fin 4 → ℤ → Fin 6) : Tapes 52 2 :=
  (⟨fun _ => 0,ss⟩ : Tapes 4 2).append (RadixLinearCombinationBootstrap.empty 48)

def common (ss : Fin 4 → ℤ → Fin 6) (source : ℤ → Fin 6)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) : Tapes 63 2 :=
  (ButterflyStreamCleanData.bank (data ss) bs ls).append
    ((CountedLoopReuseAlphabet.one source 0).append (RecursiveRowsRoleBank.headers hs))

def splitPorts : Fin 9 → Fin 63 := ![56,0,1,57,58,59,60,61,62]
def mergePorts : Fin 9 → Fin 63 := ![56,2,3,57,58,59,60,61,62]

theorem splitPorts_injective : Function.Injective splitPorts := by decide
theorem mergePorts_injective : Function.Injective mergePorts := by decide

def bank (ss : Fin 4 → ℤ → Fin 6) (source : ℤ → Fin 6)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) :=
  (common ss source bs ls hs).append (SharedBank.empty LocalTapes 2)

def word (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) :=
  full (fun _ => blank) 0 (ButterflyAxisSerialization.joined xs)

def role (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) (j : Fin 2) :=
  full (fun _ => blank) 0 (ButterflyAxisSerialization.paired xs j)

def blankStreams : Fin 4 → ℤ → Fin 6 := fun _ _ => blank
def inputStreams (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) :=
  ![role xs 0,role xs 1,fun _ => blank,fun _ => blank]
def outputStreams (xs : Fin (groups 2 v) → Fin 2 → Fin N → Coefficient) :=
  ![fun _ => blank,fun _ => blank,role xs 0,role xs 1]

theorem split_payload (ss : Fin 4 → ℤ → Fin 6) (source : ℤ → Fin 6)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) :
    SharedBank.payload (common ss source bs ls hs) splitPorts=
      (CyclicRowCopy.payload source ![ss 0,ss 1] 0 (fun _ => 0)).append
        (RecursiveRowsRoleBank.headers hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem merge_payload (ss : Fin 4 → ℤ → Fin 6) (source : ℤ → Fin 6)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) :
    SharedBank.payload (common ss source bs ls hs) mergePorts=
      (CyclicRowCopy.payload source ![ss 2,ss 3] 0 (fun _ => 0)).append
        (RecursiveRowsRoleBank.headers hs) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem strip_eq (ports : Fin 9 → Fin 63) (ss tt : Fin 4 → ℤ → Fin 6)
    (source target : ℤ → Fin 6) (bs ls : List Bool) (hs : Fin 6 → List Bool)
    (hp : ∃ j,ports j=56)
    (hframe : ∀ i : Fin 4,ss i=tt i ∨ ∃ j,ports j=⟨i.val,by omega⟩) :
    SharedBank.strip (common ss source bs ls hs) ports=
      SharedBank.strip (common tt target bs ls hs) ports := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      induction i using (Fin.addCases (m:=56) (n:=7)) with
      | left i =>
        induction i using (Fin.addCases (m:=54) (n:=2)) with
        | left i =>
          induction i using (Fin.addCases (m:=52) (n:=2)) with
          | left i =>
            induction i using (Fin.addCases (m:=4) (n:=48)) with
            | left i =>
              rcases hframe i with he | he
              · simpa only [common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,ButterflyStreamCleanData.original,data,Tapes.append,Fin.addCases_left] using he
              · exact (hi he).elim
            | right i => simp only [common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,ButterflyStreamCleanData.original,data,Tapes.append,Fin.addCases_left,Fin.addCases_right]
          | right i => simp only [common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,ButterflyStreamCleanData.original,data,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,ButterflyStreamCleanData.original,data,Tapes.append,Fin.addCases_left,Fin.addCases_right]
      | right i =>
        induction i using (Fin.addCases (m:=1) (n:=6)) with
        | left i => fin_cases i; exact (hi hp).elim
        | right i => simp only [common,ButterflyStreamCleanData.bank,CountedLoopHeaderClean.bank,ButterflyStreamCleanData.original,data,Tapes.append,Fin.addCases_right]

theorem split_frame (ss tt : Fin 4 → ℤ → Fin 6) (source target : ℤ → Fin 6)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) (h2 : ss 2=tt 2) (h3 : ss 3=tt 3) :
    SharedBank.strip (common ss source bs ls hs) splitPorts=
      SharedBank.strip (common tt target bs ls hs) splitPorts := by
  apply strip_eq splitPorts ss tt source target bs ls hs ⟨0,rfl⟩
  intro i
  fin_cases i
  · exact Or.inr ⟨1,rfl⟩
  · exact Or.inr ⟨2,rfl⟩
  · exact Or.inl h2
  · exact Or.inl h3

theorem merge_frame (ss tt : Fin 4 → ℤ → Fin 6) (source target : ℤ → Fin 6)
    (bs ls : List Bool) (hs : Fin 6 → List Bool) (h0 : ss 0=tt 0) (h1 : ss 1=tt 1) :
    SharedBank.strip (common ss source bs ls hs) mergePorts=
      SharedBank.strip (common tt target bs ls hs) mergePorts := by
  apply strip_eq mergePorts ss tt source target bs ls hs ⟨0,rfl⟩
  intro i
  fin_cases i
  · exact Or.inl h0
  · exact Or.inl h1
  · exact Or.inr ⟨1,rfl⟩
  · exact Or.inr ⟨2,rfl⟩

end
end IntegerMultBounds.Machine.ButterflyAxisBank
