import IntegerMultBounds.Machine.Gather
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.GrowingCounterData

/-! A fixed finite-state field gather. A runtime binary descriptor counts the
mapped field cells; the control head stays fixed and both countdown controls
are restored exactly. No field length or stride is compiled into the program. -/
namespace IntegerMultBounds.Machine.CountedGatherField
variable {a : ℕ}

/-- Three payload tapes and two reusable binary countdown tapes. -/
def program (op : Bool → Bool → Bool) (a : ℕ) : Program 5 18 a :=
  CountedLoopReuseAlphabet.program (Gather.opCell op a)

def state (op : Bool → Bool → Bool) (xs : List Bool) (z : Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (start i : ℕ) : Tapes 3 a :=
  Gather.bank (putWord f px (xs.map bitSymbol)) g
    (putWord h pt (((Gather.field xs start i).map (fun x => op x z)).map bitSymbol))
    (px+start+i) pz (pt+i)

private theorem cell_hoare (op : Bool → Bool → Bool) (xs : List Bool) (z : Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (start d i : ℕ)
    (hd : start+d ≤ xs.length) (hi : i < d) (hz : g pz = bitSymbol z) :
    HoareTime (Gather.opCell op a)
      (fun v => v = state op xs z f g h px pz pt start i)
      (fun v => v = state op xs z f g h px pz pt start (i+1)) 1 := by
  have hc := Gather.opCell_hoare op (putWord f px (xs.map bitSymbol)) g
    (putWord h pt (((Gather.field xs start i).map (fun x => op x z)).map bitSymbol))
    (px+start+i) pz (pt+i) (xs.getD (start+i) false) z
    (by rw [show px+(start : ℤ)+i = px+((start+i : ℕ) : ℤ) by push_cast; ring,
      Gather.putWord_getD _ _ _ _ (by omega)]) hz
  apply hc.consequence (fun _ he => he) _ le_rfl
  rintro v rfl
  have hl : pt+(i : ℤ) =
      pt+(((Gather.field xs start i).map (fun x => op x z)).map (bitSymbol (a := a))).length := by
    simp only [List.length_map,Gather.field_length]
  rw [hl,Gather.putWord_snoc]
  unfold state
  simp only [Gather.field_succ,List.map_append,List.map_singleton]
  congr 1
  all_goals first | rfl | ((try simp only [List.length_map,Gather.field_length]); push_cast; ring)

/-- Literal field semantics for every runtime descriptor, including zero:
the source and control tapes survive, source/target advance by the field
length, and the descriptor and reusable clock return to their input banks. -/
theorem field_hoare (op : Bool → Bool → Bool) (xs : List Bool) (z : Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (start d : ℕ) (bs : List Bool)
    (hd : start+d ≤ xs.length) (hz : g pz = bitSymbol z) (hcount : Counter.value bs = d) :
    HoareTime (program op a)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) g h (px+start) pz pt)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) g
          (putWord h pt (((Gather.field xs start d).map (fun x => op x z)).map bitSymbol))
          (px+start+d) pz (pt+d))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (7*d+7*bs.length+16) := by
  have hc := CountedLoopReuseAlphabet.loop_hoare (Gather.opCell op a) bs d
    (state op xs z f g h px pz pt start) (fun _ => 1) hcount
    (fun i hi => cell_hoare op xs z f g h px pz pt start d i hd hi hz)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] at hc
  have hcost : d+6*d+7*bs.length+16 = 7*d+7*bs.length+16 := by omega
  rw [hcost] at hc
  simpa only [program,state,Gather.field_zero,List.map_nil,putWord,
    Nat.cast_zero,add_zero] using hc

/-- Canonical runtime headers give a paid linear field bound. -/
theorem linear_bound (d : ℕ) (bs : List Bool) (hcount : Counter.value bs = d)
    (hc : GrowingCounterData.Canonical bs) : 7*d+7*bs.length+16 ≤ 14*d+23 := by
  have hw := GrowingCounterData.canonical_width bs hc
  have hl := Nat.log2_le_self (Counter.value bs)
  rw [hcount] at hw hl
  omega

/-- A convenient canonical-header contract with the same exact bank endpoints. -/
theorem field_hoare_linear (op : Bool → Bool → Bool) (xs : List Bool) (z : Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (start d : ℕ) (bs : List Bool)
    (hd : start+d ≤ xs.length) (hz : g pz = bitSymbol z) (hcount : Counter.value bs = d)
    (hc : GrowingCounterData.Canonical bs) :
    HoareTime (program op a)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) g h (px+start) pz pt)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) g
          (putWord h pt (((Gather.field xs start d).map (fun x => op x z)).map bitSymbol))
          (px+start+d) pz (pt+d))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (14*d+23) :=
  (field_hoare op xs z f g h px pz pt start d bs hd hz hcount).consequence
    (fun _ he => he) (fun _ he => he) (linear_bound d bs hcount hc)

/-- A whole word is the field starting at zero. -/
theorem field_whole (xs : List Bool) : Gather.field xs 0 xs.length = xs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [Gather.field,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2]

/-- Whole-word specialization, convenient for nested runtime digit loops. -/
theorem word_hoare (op : Bool → Bool → Bool) (xs : List Bool) (z : Bool)
    (f g h : ℤ → Fin (a+4)) (px pz pt : ℤ) (bs : List Bool)
    (hz : g pz = bitSymbol z) (hcount : Counter.value bs = xs.length) :
    HoareTime (program op a)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) g h px pz pt)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (fun v => v = CountedLoopReuseAlphabet.bank
        (Gather.bank (putWord f px (xs.map bitSymbol)) g
          (putWord h pt ((xs.map (fun x => op x z)).map bitSymbol))
          (px+xs.length) pz (pt+xs.length))
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1)
      (7*xs.length+7*bs.length+16) := by
  simpa only [field_whole,Nat.cast_zero,add_zero] using
    field_hoare op xs z f g h px pz pt 0 xs.length bs (by omega) hz hcount

end IntegerMultBounds.Machine.CountedGatherField
