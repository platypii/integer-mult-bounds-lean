import IntegerMultBounds.Machine.CompactReservationPaddingHeaders
import IntegerMultBounds.Machine.CompactReservedOriginal
import IntegerMultBounds.Machine.NativeZeroPaddingArray

/-! Actual global reservation executes on the original binary word before
one native zero pad. Runtime metadata is computed from retained original
scalars, every generated field is erased, and the native source returns to0. -/
namespace IntegerMultBounds.Machine.CompactReservationNativePadding
noncomputable section
open CompactReservationPaddingHeaders (prepared width)
open CompactReservedHeaders (initial)
open CompactGlobalRowPadding
open RecursiveChildQuotientsConstant (bits)
open CompactFallbackAxisRun (Array Width)

abbrev commonCount := 44+CompactReservedAxisPorts.count+2

def ports : Fin 6 → Fin 51 := ![43,0,1,2,3,4]
def focus (i : Fin 6) : Fin commonCount :=
  ⟨(![43,12,13,15,3,17] i : Fin 44).val,by
    have hi := (![43,12,13,15,3,17] i : Fin 44).isLt
    unfold commonCount
    omega⟩
theorem ports_injective : Function.Injective ports := by decide
theorem focus_injective : Function.Injective focus := by decide

def originalBank (st : ActiveRepairRankHeadersCommands.State) (xs : List (Fin 6)) :=
  CompactReservedSchedule.bank st (NativeZeroPadding.word xs)
def bank (st : ActiveRepairRankHeadersCommands.State) (xs : List (Fin 6)) :=
  (originalBank st xs).append (SharedBank.empty 51 2)
def padProgram := Placement.placed NativeZeroPaddingPlaced.program
  (CleanSubbank.placement ports focus focus_injective)
def headerProgram (ops : List CompactGlobalRowHeaderOps.Op) :=
  extend (extend (extend (extend (CompactGlobalRowHeaderOps.compile (a:=2) ops).2 1)
    CompactReservedAxisPorts.count) 2) 51
def program (inverse : Bool) (c m : ℕ) :=
  seq (seq (seq (extend (CompactReservedOriginal.program inverse c m) 51)
    (headerProgram (CompactReservationPaddingHeaders.schedule c m))) padProgram)
    (headerProgram CompactReservationPaddingHeaders.cleanup)

def count (c m d D K ell : ℕ) := NativeZeroPaddingHeaders.count (originalRows c m d K)
  (initialRows c m d K) ((D-rowAxes c m d)*K) ell
def result (inverse : Bool) (c m D K rho ell q d G : ℕ) (f : Array D K ell) :=
  NativeZeroPaddingArray.word (CompactReservedOriginal.result inverse c m D K rho ell q d G f)++
    NativeZeroStream.records (width D K q) (count c m d D K ell)

theorem small_clean (rows target D ell w : ℕ) (xs : List (Fin 6)) :
    SharedBank.strip (NativeZeroPaddingPlaced.bank (NativeZeroPaddingHeaders.initial rows target D ell w) xs) ports=
      SharedBank.empty 51 2 := by
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simp only [hi,ite_false]
      fin_cases i
      all_goals first | rfl | exact (hi ⟨0,rfl⟩).elim | exact (hi ⟨1,rfl⟩).elim |
        exact (hi ⟨2,rfl⟩).elim | exact (hi ⟨3,rfl⟩).elim | exact (hi ⟨4,rfl⟩).elim | exact (hi ⟨5,rfl⟩).elim
  · funext i
    by_cases hi : ∃ j,ports j=i
    · simp [hi]
    · simp only [hi,ite_false]
      fin_cases i
      all_goals first | rfl | exact (hi ⟨0,rfl⟩).elim | exact (hi ⟨1,rfl⟩).elim |
        exact (hi ⟨2,rfl⟩).elim | exact (hi ⟨3,rfl⟩).elim | exact (hi ⟨4,rfl⟩).elim | exact (hi ⟨5,rfl⟩).elim

theorem payload (c m D K rho ell q d G : ℕ) (xs : List (Fin 6)) :
    SharedBank.payload (NativeZeroPaddingPlaced.bank (NativeZeroPaddingHeaders.initial (originalRows c m d K)
      (initialRows c m d K) ((D-rowAxes c m d)*K) ell (width D K q)) xs) ports=
      SharedBank.payload (originalBank (prepared c m D K rho ell q d G) xs) focus := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem frame (st : ActiveRepairRankHeadersCommands.State) (xs ys : List (Fin 6)) :
    SharedBank.strip (originalBank st xs) focus=SharedBank.strip (originalBank st ys) focus := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    by_cases hi : ∃ j,focus j=i
    · simp only [hi,ite_true]
    · simp only [hi,ite_false]
      induction i using (Fin.addCases (m:=44+CompactReservedAxisPorts.count) (n:=2)) with
      | right i => simp only [originalBank,CompactReservedSchedule.bank,CountedLoopHeaderClean.bank,Tapes.append,Fin.addCases_right]
      | left i =>
        induction i using (Fin.addCases (m:=44) (n:=CompactReservedAxisPorts.count)) with
        | right i => simp only [originalBank,CompactReservedSchedule.bank,CountedLoopHeaderClean.bank,CompactReservedAxisRun.bank,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        | left i =>
          fin_cases i
          all_goals first | rfl | exact (hi ⟨0,rfl⟩).elim

theorem pad_runs (c m D K rho ell q d G : ℕ) (hc : 0<c) (hK : 0<K)
    (xs : List (Fin 6)) (hn : ∀ x∈xs,x≠blank) :
    HoareTime padProgram
      (fun v => v=bank (prepared c m D K rho ell q d G) xs)
      (fun v => v=bank (prepared c m D K rho ell q d G)
        (xs++NativeZeroStream.records (width D K q) (count c m d D K ell)))
      (NativeZeroPaddingPlaced.cost (originalRows c m d K) (initialRows c m d K)
        ((D-rowAxes c m d)*K) ell (width D K q) xs) := by
  have hh := NativeZeroPaddingPlaced.runs (originalRows c m d K) (initialRows c m d K)
    ((D-rowAxes c m d)*K) ell (width D K q) (initial_bounds c m d K hc hK).1 xs hn
  apply CleanSubbank.realizes (c:=6) (s:=51) (k:=commonCount) NativeZeroPaddingPlaced.program
    ports focus ports_injective focus_injective
    (originalBank (prepared c m D K rho ell q d G) xs)
    (originalBank (prepared c m D K rho ell q d G) (xs++NativeZeroStream.records (width D K q) (count c m d D K ell)))
    _ _ _ ?_ ?_ ?_ ?_ ?_ hh
  · exact payload c m D K rho ell q d G xs
  · exact payload c m D K rho ell q d G _
  · exact small_clean _ _ _ _ _ _
  · exact small_clean _ _ _ _ _ _
  · exact frame _ _ _

def cost (inverse : Bool) (c m D K rho ell q d G : ℕ) (f : Array D K ell) :=
  CompactReservedOriginal.cost c m D K rho ell q d G+
  CompactGlobalRowHeaderOps.scheduleCost (CompactReservationPaddingHeaders.schedule c m) (initial D K rho ell q d G)+
  NativeZeroPaddingPlaced.cost (originalRows c m d K) (initialRows c m d K) ((D-rowAxes c m d)*K) ell (width D K q)
    (NativeZeroPaddingArray.word (CompactReservedOriginal.result inverse c m D K rho ell q d G f))+
  CompactGlobalRowHeaderOps.scheduleCost CompactReservationPaddingHeaders.cleanup (prepared c m D K rho ell q d G)+3

theorem runs (inverse : Bool) (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hr : rho<K) (hDp : 0<D)
    (hD : CompactReservedHeaders.reserved c m d G K≤D) (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime (program inverse c m)
      (fun v => v=bank (initial D K rho ell q d G) (NativeZeroPaddingArray.word f))
      (fun v => v=bank (initial D K rho ell q d G) (result inverse c m D K rho ell q d G f))
      (cost inverse c m D K rho ell q d G f) := by
  let g := CompactReservedOriginal.result inverse c m D K rho ell q d G f
  have hrow : rowAxes c m d≤D := by unfold CompactReservedHeaders.reserved CompactReservedHeaders.high at hD; omega
  have h0 := hoare_extend_eq (CompactReservedOriginal.runs inverse c m D K rho ell q d G hc hm hd hK hr hD f hw)
    (SharedBank.empty 51 2)
  have h1 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactReservationPaddingHeaders.runs c m D K rho ell q d G hc hm hd hK hrow hDp)
    (CountedLoopReuseAlphabet.one (NativeZeroPadding.word (NativeZeroPaddingArray.word g)) 0))
    (SharedBank.empty CompactReservedAxisPorts.count 2)) (SharedBank.empty 2 2)) (SharedBank.empty 51 2)
  have h2 := pad_runs c m D K rho ell q d G (by omega) hK (NativeZeroPaddingArray.word g)
    (fun x hx => NativeZeroPaddingArray.nonblank g x hx)
  have h3 := hoare_extend_eq (hoare_extend_eq (hoare_extend_eq (hoare_extend_eq
    (CompactReservationPaddingHeaders.cleanup_runs c m D K rho ell q d G)
    (CountedLoopReuseAlphabet.one (NativeZeroPadding.word (result inverse c m D K rho ell q d G f)) 0))
    (SharedBank.empty CompactReservedAxisPorts.count 2)) (SharedBank.empty 2 2)) (SharedBank.empty 51 2)
  exact (((h0.seq h1).seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; dsimp only [g]; omega)

/-- The computed padding count extends original binary coefficients to one
whole globally padded row representation, retaining every address spectator. -/
theorem coefficient_cardinality (c m d D K ell : ℕ) (hc : 0<c) (hK : 0<K) (hrow : rowAxes c m d≤D) :
    2^(D*K)*2^ell+count c m d D K ell=initialRows c m d K*2^((D-rowAxes c m d)*K)*2^ell := by
  have he := congrArg (fun n => n*K) (Nat.add_sub_of_le hrow)
  simp only [Nat.add_mul] at he
  have hv : originalRows c m d K*2^((D-rowAxes c m d)*K)*2^ell=2^(D*K)*2^ell := by
    unfold originalRows
    rw [←pow_add,he]
  have hh := NativeZeroPaddingHeaders.added_volume (originalRows c m d K) (initialRows c m d K)
    ((D-rowAxes c m d)*K) ell (initial_bounds c m d K hc hK).1
  unfold count
  rw [←hv]
  exact hh

end
end IntegerMultBounds.Machine.CompactReservationNativePadding
