import IntegerMultBounds.Machine.ActiveRepairRankHeadersArithmetic

/-! A finite descriptor-arithmetic schedule compiles to actual copy, addition,
subtraction, constant-initialization and erase machines with clean workspace. -/
namespace IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

abbrev State := Fin 28 → Option ℕ
inductive Command where
  | copy (src dst : Fin 28) (distinct : src≠dst)
  | add (dst src : Fin 28) (distinct : dst≠src)
  | difference (src small dst : Fin 28) (distinct : Function.Injective (![src,small,dst] : Fin 3 → Fin 28))
  | zero (dst : Fin 28)
  | erase (dst : Fin 28)

def caller (st : State) : Tapes 28 a :=
  ⟨fun i => if (st i).isSome then 1 else 0,
    fun i => match st i with | none => fun _ => blank | some n => RadixZeroFill.encodedBinary (bits n)⟩
def bank (st : State) := CleanSubbank.bank (s := 15) (caller (a := a) st)

def put (st : State) (i : Fin 28) (n : ℕ) := Function.update st i (some n)
def eval (c : Command) (st : State) : State := match c with
  | .copy src dst _ => put st dst ((st src).getD 0)
  | .add dst src _ => put st dst ((st dst).getD 0+(st src).getD 0)
  | .difference src small dst _ => put st dst ((st src).getD 0-(st small).getD 0)
  | .zero dst => put st dst 0
  | .erase dst => Function.update st dst none

def valid (c : Command) (st : State) : Prop := match c with
  | .copy src dst _ => ∃ n, st src=some n ∧ st dst=none
  | .add dst src _ => ∃ n m, st dst=some n ∧ st src=some m
  | .difference src small dst _ => ∃ n m, st src=some n ∧ st small=some m ∧ st dst=none ∧ m≤n
  | .zero dst => st dst=none
  | .erase dst => ∃ n, st dst=some n

def two (i j : Fin 28) : Fin 2 → Fin 28 := ![i,j]
theorem two_injective (i j : Fin 28) (h : i≠j) : Function.Injective (two i j) := by
  intro x y he; fin_cases x <;> fin_cases y <;> simp_all [two]

def one (c : Command) : Σ k, Program 43 k a := match c with
  | .copy src dst h => ⟨_,extend (BinaryDescriptorCopyPlaced.program (two src dst) (two_injective src dst h)) 15⟩
  | .add dst src h => ⟨_,ActiveRepairRankHeadersArithmetic.addProgram (two dst src) (two_injective dst src h)⟩
  | .difference src small dst h => ⟨_,CompactGadgetReservationHeadersCore.differenceProgram ![src,small,dst] h⟩
  | .zero dst => ⟨_,extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 0)
      (FiniteReturnStackAt.placement dst)) 15⟩
  | .erase dst => ⟨_,extend (BinaryDescriptorCleanupList.oneProgram (a := a) dst) 15⟩

def cost (c : Command) (st : State) := 100*(match c with
  | .copy src _ _ => (st src).getD 0+1
  | .add dst src _ => (st dst).getD 0+(st src).getD 0+1
  | .difference src small _ _ => (st src).getD 0+(st small).getD 0+1
  | .zero _ => 1
  | .erase dst => (st dst).getD 0+1)

theorem put_caller (st : State) (i : Fin 28) (n : ℕ) :
    caller (a := a) (put st i n)=setTape (caller st) i (RadixZeroFill.encodedBinary (bits n)) 1 := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j=i <;> simp [caller,put,Function.update,hj]

theorem erase_caller (st : State) (i : Fin 28) :
    caller (a := a) (Function.update st i none)=setTape (caller st) i (fun _ => blank) 0 := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j=i <;> simp [caller,Function.update,hj]

theorem bits_length (n : ℕ) : (bits n).length≤n+1 :=
  (GrowingCounterData.canonical_width _ (RecursiveChildQuotientsConstant.bits_canonical n)).trans
    (by rw [RecursiveChildQuotientsConstant.bits_value]; exact Nat.add_le_add_right (Nat.log2_le_self n) 1)

theorem runs (c : Command) (st : State) (hv : valid c st) :
    HoareTime (one (a := a) c).2 (fun x => x=bank st)
      (fun x => x=bank (eval c st)) (cost c st) := by
  cases c with
  | copy src dst hd =>
    obtain ⟨n,hs,ht⟩ := hv
    have hi : SharedBank.payload (caller (a := a) st) (two src dst)=BinaryDescriptorCopy.encodedInput a (bits n) := by
      apply congrArg₂ Tapes.mk <;> funext j <;> fin_cases j <;> simp [caller,two,hs,ht] <;> rfl
    have h := hoare_extend_eq (BinaryDescriptorCopyPlaced.copies (caller (a := a) st)
      (two src dst) (two_injective src dst hd) (bits n) hi) (SharedBank.empty 15 a)
    have he : eval (.copy src dst hd) st=put st dst n := by simp [eval,hs]
    rw [he]
    have hl := bits_length n
    exact h.consequence (fun _ h => h) (fun _ h => by simpa [bank,put_caller,two,CleanSubbank.bank] using h)
      (by simp [cost,hs]; omega)
  | add dst src hd =>
    obtain ⟨n,m,hs,ht⟩ := hv
    have h := ActiveRepairRankHeadersArithmetic.adds (caller (a := a) st) (two dst src)
      (two_injective dst src hd) (bits n) (bits m) (RecursiveChildQuotientsConstant.bits_canonical n)
      (by simp [caller,two,hs]) (by simp [caller,two,hs])
      (by simp [caller,two,ht]) (by simp [caller,two,ht])
    simp only [RecursiveChildQuotientsConstant.bits_value] at h
    have he : eval (.add dst src hd) st=put st dst (n+m) := by simp [eval,hs,ht]
    rw [he]
    have hn := bits_length n
    have hm := bits_length m
    exact h.consequence (fun _ h => h) (fun _ h => by simpa [bank,put_caller,two,CompactGadgetReservationHeadersCore.bank] using h)
      (by simp [cost,hs,ht]; omega)
  | difference src small dst hd =>
    obtain ⟨n,m,hs,ht,hz,hmn⟩ := hv
    have h := CompactGadgetReservationHeadersCore.difference (caller (a := a) st) ![src,small,dst] hd
      (bits n) (bits m) (by simpa only [RecursiveChildQuotientsConstant.bits_value] using hmn) (RecursiveChildQuotientsConstant.bits_canonical n)
      (RecursiveChildQuotientsConstant.bits_canonical m)
      (by simp [caller,hs]) (by simp [caller,hs])
      (by simp [caller,ht]) (by simp [caller,ht])
      (by simp [caller,hz]) (by simp [caller,hz])
    simp only [RecursiveChildQuotientsConstant.bits_value] at h
    have he : eval (.difference src small dst hd) st=put st dst (n-m) := by simp [eval,hs,ht]
    rw [he]
    exact h.consequence (fun _ h => h) (fun _ h => by simpa [bank,put_caller,CompactGadgetReservationHeadersCore.bank] using h)
      (by simp [cost,hs,ht]; omega)
  | zero dst =>
    change st dst=none at hv
    have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 0)
      (FiniteReturnStackAt.placement dst) (caller (a := a) st)
      (by rw [FiniteReturnStackAt.active_bank]; simp [caller,hv])
    have h' : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 0)
        (FiniteReturnStackAt.placement dst)) (fun x => x=caller st)
        (fun x => x=caller (put st dst 0)) 6 := by
      apply h.consequence (fun _ h => h) _ le_rfl
      rintro z ⟨small,rfl,rfl⟩
      rw [put_caller,FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    exact (hoare_extend_eq h' (SharedBank.empty 15 a)).consequence
      (fun _ h => h) (fun _ h => h) (by simp [cost])
  | erase dst =>
    obtain ⟨n,hn⟩ := hv
    have h := BinaryDescriptorCleanupList.one_hoare dst (caller (a := a) st) (bits n)
      (by simp [caller,hn,BinaryDescriptorStackRoundtrip.descriptor_encoded]) (by simp [caller,hn])
    have hl := bits_length n
    exact (hoare_extend_eq h (SharedBank.empty 15 a)).consequence (fun _ h => h)
      (fun _ h => by simpa only [bank,eval,erase_caller,CleanSubbank.bank] using h) (by simp [cost,hn]; omega)

def compile : List Command → Σ k, Program 43 k a
  | [] => ⟨1,skip 43 a (by decide)⟩
  | c::cs => ⟨_,seq (one c).2 (compile cs).2⟩
def execute : List Command → State → State
  | [],st => st
  | c::cs,st => execute cs (eval c st)
def validSchedule : List Command → State → Prop
  | [],_ => True
  | c::cs,st => valid c st ∧ validSchedule cs (eval c st)
def scheduleCost : List Command → State → ℕ
  | [],_ => 0
  | c::cs,st => cost c st+1+scheduleCost cs (eval c st)

theorem schedule_runs (cs : List Command) (st : State) (hv : validSchedule cs st) :
    HoareTime (compile (a := a) cs).2 (fun x => x=bank st)
      (fun x => x=bank (execute cs st)) (scheduleCost cs st) := by
  induction cs generalizing st with
  | nil => exact skip_hoare (by decide) (bank st)
  | cons c cs ih => exact (runs c st hv.1).seq (ih (eval c st) hv.2)

def Bounded (st : State) (A : ℕ) := ∀ i, (st i).getD 0≤A

theorem eval_bounded (c : Command) (st : State) (A : ℕ) (hb : Bounded st A) :
    Bounded (eval c st) (2*A) := by
  intro i
  cases c with
  | copy src dst h =>
    by_cases hi : i=dst <;> simp [eval,put,Function.update,hi]
    · exact (hb src).trans (by omega)
    · exact (hb i).trans (by omega)
  | add dst src h =>
    by_cases hi : i=dst <;> simp [eval,put,Function.update,hi]
    · have h0 := hb dst; have h1 := hb src; omega
    · exact (hb i).trans (by omega)
  | difference src small dst h =>
    by_cases hi : i=dst <;> simp [eval,put,Function.update,hi]
    · have h0 := hb src
      have hsub := Nat.sub_le ((st src).getD 0) ((st small).getD 0)
      omega
    · exact (hb i).trans (by omega)
  | zero dst =>
    by_cases hi : i=dst <;> simp [eval,put,Function.update,hi]
    exact (hb i).trans (by omega)
  | erase dst =>
    by_cases hi : i=dst <;> simp [eval,Function.update,hi]
    exact (hb i).trans (by omega)

theorem cost_bounded (c : Command) (st : State) (A : ℕ) (hb : Bounded st A) :
    cost c st≤200*A+100 := by
  cases c with
  | copy src dst h => simp only [cost]; have h0 := hb src; omega
  | add dst src h => simp only [cost]; have h0 := hb src; have h1 := hb dst; omega
  | difference src small dst h => simp only [cost]; have h0 := hb src; have h1 := hb small; omega
  | zero dst => simp only [cost]; omega
  | erase dst => simp only [cost]; have h0 := hb dst; omega

/-- A fixed arithmetic schedule has a linear bound in the supplied numeric
width bound. The coefficient depends only on its finite command list. -/
theorem scheduleCost_bounded (cs : List Command) (st : State) (A : ℕ) (hb : Bounded st A) :
    scheduleCost cs st≤300*3^cs.length*(A+1) := by
  induction cs generalizing st A with
  | nil => simp [scheduleCost]
  | cons c cs ih =>
    have h0 := cost_bounded c st A hb
    have h1 := ih (eval c st) (2*A) (eval_bounded c st A hb)
    have hp : 1≤3^cs.length := Nat.one_le_pow _ _ (by decide)
    simp only [scheduleCost,List.length_cons,pow_succ]
    nlinarith

end
end IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands
