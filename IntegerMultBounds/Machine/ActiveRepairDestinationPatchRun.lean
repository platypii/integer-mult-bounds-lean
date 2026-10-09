import IntegerMultBounds.Machine.ActiveRepairDestinationPatchData
import IntegerMultBounds.Machine.ActiveRepairDestinationPatchPlaced
import IntegerMultBounds.Machine.ActiveRepairRankFieldsPlaced

/-! Full-width rank reconstruction from the genuine short counter, followed by
three runtime field replacements. Twelve caller slots share nine erased slots. -/
namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchRun
noncomputable section
open SharedPlacementAlphabet (setTape)

def word (xs : List Bool) : ℤ → Fin 5 := putWord (fun _ => blank) 0 (xs.map bitSymbol)

def bank (cs v t u : List Bool) (g : ℤ → Fin 5) (hs : Fin 7 → List Bool) : Tapes 12 1 :=
  ⟨![1,0,0,0,0,1,1,1,1,1,1,1],
    ![RepairScan.ctrTape cs,g,word v,word t,word u,
      RadixZeroFill.encodedBinary (hs 0),RadixZeroFill.encodedBinary (hs 1),
      RadixZeroFill.encodedBinary (hs 2),RadixZeroFill.encodedBinary (hs 3),
      RadixZeroFill.encodedBinary (hs 4),RadixZeroFill.encodedBinary (hs 5),
      RadixZeroFill.encodedBinary (hs 6)]⟩

def initFocus : Fin 4 → Fin 12 := ![0,1,5,6]
def vFocus : Fin 4 → Fin 12 := ![2,1,7,8]
def tFocus : Fin 4 → Fin 12 := ![3,1,9,10]
def uFocus : Fin 4 → Fin 12 := ![4,1,11,10]
theorem init_injective : Function.Injective initFocus := by decide
theorem v_injective : Function.Injective vFocus := by decide
theorem t_injective : Function.Injective tFocus := by decide
theorem u_injective : Function.Injective uFocus := by decide

def initHeaders (hs : Fin 7 → List Bool) : Fin 2 → List Bool := ![hs 0,hs 1]
def vHeaders (hs : Fin 7 → List Bool) : Fin 2 → List Bool := ![hs 2,hs 3]
def tHeaders (hs : Fin 7 → List Bool) : Fin 2 → List Bool := ![hs 4,hs 5]
def uHeaders (hs : Fin 7 → List Bool) : Fin 2 → List Bool := ![hs 6,hs 5]

def program := seq (seq (seq
  (ActiveRepairRankFieldsPlaced.program initFocus init_injective)
  (ActiveRepairDestinationPatchPlaced.program vFocus v_injective))
  (ActiveRepairDestinationPatchPlaced.program tFocus t_injective))
  (ActiveRepairDestinationPatchPlaced.program uFocus u_injective)

def initial (cs : List Bool) (total : ℕ) := Gather.field cs 0 total

def destination (cs v t u : List Bool) (total sv st su : ℕ) :=
  ActiveRepairDestinationPatchData.patch
    (ActiveRepairDestinationPatchData.patch
      (ActiveRepairDestinationPatchData.patch (initial cs total) sv v) st t) su u

def cost (total sv st su : ℕ) (v t u : List Bool) (hs : Fin 7 → List Bool) :=
  ActiveRepairRankFieldsField.cost 0 total (initHeaders hs)+
    ActiveRepairRankFieldsField.cost sv v.length (vHeaders hs)+
    ActiveRepairRankFieldsField.cost st t.length (tHeaders hs)+
    ActiveRepairRankFieldsField.cost su u.length (uHeaders hs)+3

theorem init_runs (cs v t u : List Bool) (g : ℤ → Fin 5) (hs : Fin 7 → List Bool)
    (total : ℕ) (hz : Counter.value (hs 0)=0) (hw : Counter.value (hs 1)=total) :
    HoareTime (ActiveRepairRankFieldsPlaced.program initFocus init_injective)
      (fun x => x=CleanSubbank.bank (s := 9) (bank cs v t u g hs))
      (fun x => x=CleanSubbank.bank (s := 9)
        (bank cs v t u (putWord g 0 ((initial cs total).map bitSymbol)) hs))
      (ActiveRepairRankFieldsField.cost 0 total (initHeaders hs)) := by
  have hp : SharedBank.payload (bank cs v t u g hs) initFocus=
      ActiveRepairRankFieldsPlaced.sources cs g (initHeaders hs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h := ActiveRepairRankFieldsPlaced.runs (bank cs v t u g hs) initFocus init_injective
    g cs (initHeaders hs) 0 total hp hz hw
  have he : ActiveRepairRankFieldsPlaced.result (bank cs v t u g hs) initFocus g cs 0 total=
      bank cs v t u (putWord g 0 ((initial cs total).map bitSymbol)) hs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

 theorem patch_runs (cs v t u : List Bool) (g : ℤ → Fin 5) (hs : Fin 7 → List Bool)
    (focus : Fin 4 → Fin 12) (hf : Function.Injective focus) (xs : List Bool)
    (hh : Fin 2 → List Bool) (start : ℕ)
    (hp : SharedBank.payload (bank cs v t u g hs) focus=
      ActiveRepairDestinationPatchPlaced.sources xs g hh)
    (hout : focus 1=1) (hv0 : Counter.value (hh 0)=start) (hv1 : Counter.value (hh 1)=xs.length) :
    HoareTime (ActiveRepairDestinationPatchPlaced.program focus hf)
      (fun x => x=CleanSubbank.bank (s := 9) (bank cs v t u g hs))
      (fun x => x=CleanSubbank.bank (s := 9)
        (bank cs v t u (putWord g start (xs.map bitSymbol)) hs))
      (ActiveRepairRankFieldsField.cost start xs.length hh) := by
  have h := ActiveRepairDestinationPatchPlaced.runs (bank cs v t u g hs) focus hf g xs hh start hp hv0 hv1
  have he : ActiveRepairDestinationPatchPlaced.result (bank cs v t u g hs) focus g xs start=
      bank cs v t u (putWord g start (xs.map bitSymbol)) hs := by
    unfold ActiveRepairDestinationPatchPlaced.result
    rw [hout]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

theorem runs (cs v t u : List Bool) (hs : Fin 7 → List Bool) (total sv st su : ℕ)
    (hz : Counter.value (hs 0)=0) (hA : Counter.value (hs 1)=total)
    (hsv : Counter.value (hs 2)=sv) (hv : Counter.value (hs 3)=v.length)
    (hst : Counter.value (hs 4)=st) (ht : Counter.value (hs 5)=t.length)
    (hsu : Counter.value (hs 6)=su) (hu : u.length=t.length)
    (fv : sv+v.length≤total) (ft : st+t.length≤total) (fu : su+u.length≤total) :
    HoareTime program
      (fun x => x=CleanSubbank.bank (s := 9) (bank cs v t u (fun _ => blank) hs))
      (fun x => x=CleanSubbank.bank (s := 9) (bank cs v t u
        (word (destination cs v t u total sv st su)) hs))
      (cost total sv st su v t u hs) := by
  let g0 := word (initial cs total)
  let g1 := putWord g0 sv (v.map bitSymbol)
  let g2 := putWord g1 st (t.map bitSymbol)
  let g3 := putWord g2 su (u.map bitSymbol)
  have h0 := init_runs cs v t u (fun _ => blank) hs total hz hA
  have pv : SharedBank.payload (bank cs v t u g0 hs) vFocus=
      ActiveRepairDestinationPatchPlaced.sources v g0 (vHeaders hs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have pt : SharedBank.payload (bank cs v t u g1 hs) tFocus=
      ActiveRepairDestinationPatchPlaced.sources t g1 (tHeaders hs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have pu : SharedBank.payload (bank cs v t u g2 hs) uFocus=
      ActiveRepairDestinationPatchPlaced.sources u g2 (uHeaders hs) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have h1 := patch_runs cs v t u g0 hs vFocus v_injective v (vHeaders hs) sv pv rfl hsv hv
  have h2 := patch_runs cs v t u g1 hs tFocus t_injective t (tHeaders hs) st pt rfl hst ht
  have h3 := patch_runs cs v t u g2 hs uFocus u_injective u (uHeaders hs) su pu rfl hsu (by change Counter.value (hs 5)=u.length; rw [hu]; exact ht)
  have e1 : g1=word (ActiveRepairDestinationPatchData.patch (initial cs total) sv v) := by
    simpa only [g1,g0,word,zero_add] using
      ActiveRepairDestinationPatchData.tape (a := 1) (fun _ => blank) 0 (initial cs total) sv v (by simpa [initial] using fv)
  have e2 : g2=word (ActiveRepairDestinationPatchData.patch
      (ActiveRepairDestinationPatchData.patch (initial cs total) sv v) st t) := by
    dsimp only [g2]
    rw [e1]
    simpa only [word,zero_add] using
      ActiveRepairDestinationPatchData.tape (a := 1) (fun _ => blank) 0
        (ActiveRepairDestinationPatchData.patch (initial cs total) sv v) st t (by simpa [initial] using ft)
  have he : g3=word (destination cs v t u total sv st su) := by
    dsimp only [g3]
    rw [e2]
    simpa only [word,destination,zero_add] using
      ActiveRepairDestinationPatchData.tape (a := 1) (fun _ => blank) 0
        (ActiveRepairDestinationPatchData.patch
          (ActiveRepairDestinationPatchData.patch (initial cs total) sv v) st t) su u
        (by simpa [initial] using fu)
  have h := ((h0.seq h1).seq h2).seq h3
  rw [show putWord g2 su (u.map bitSymbol)=g3 from rfl,he] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

@[simp] theorem destination_length (cs v t u : List Bool) (total sv st su : ℕ) :
    (destination cs v t u total sv st su).length=total := by simp [destination,initial]

/-- The initialization copies the actual counter rank without requiring a
padded representation or storing an already completed destination. -/
theorem initial_value (cs : List Bool) (total : ℕ) (hb : Counter.value cs<2^total) :
    Counter.value (initial cs total)=Counter.value cs := by
  rw [initial,CountedRankSplitData.value_prefix,Nat.mod_eq_of_lt hb]

theorem cost_linear (v t u : List Bool) (hs : Fin 7 → List Bool) (total sv st su : ℕ)
    (hz : Counter.value (hs 0)=0) (hA : Counter.value (hs 1)=total)
    (hsv : Counter.value (hs 2)=sv) (hv : Counter.value (hs 3)=v.length)
    (hst : Counter.value (hs 4)=st) (ht : Counter.value (hs 5)=t.length)
    (hsu : Counter.value (hs 6)=su) (hu : u.length=t.length)
    (fv : sv+v.length≤total) (ft : st+t.length≤total) (fu : su+u.length≤total)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    cost total sv st su v t u hs≤800*(total+1)+3 := by
  have c0 := ActiveRepairRankFieldsField.cost_linear 0 total (initHeaders hs) hz hA
    (by intro i; fin_cases i <;> first | exact hc 0 | exact hc 1)
  have c1 := ActiveRepairRankFieldsField.cost_linear sv v.length (vHeaders hs) hsv hv
    (by intro i; fin_cases i <;> first | exact hc 2 | exact hc 3)
  have c2 := ActiveRepairRankFieldsField.cost_linear st t.length (tHeaders hs) hst ht
    (by intro i; fin_cases i <;> first | exact hc 4 | exact hc 5)
  have c3 := ActiveRepairRankFieldsField.cost_linear su u.length (uHeaders hs) hsu
    (by change Counter.value (hs 5)=u.length; rw [hu]; exact ht)
    (by intro i; fin_cases i <;> first | exact hc 6 | exact hc 5)
  unfold cost
  omega

theorem runs_linear (cs v t u : List Bool) (hs : Fin 7 → List Bool) (total sv st su : ℕ)
    (hz : Counter.value (hs 0)=0) (hA : Counter.value (hs 1)=total)
    (hsv : Counter.value (hs 2)=sv) (hv : Counter.value (hs 3)=v.length)
    (hst : Counter.value (hs 4)=st) (ht : Counter.value (hs 5)=t.length)
    (hsu : Counter.value (hs 6)=su) (hu : u.length=t.length)
    (fv : sv+v.length≤total) (ft : st+t.length≤total) (fu : su+u.length≤total)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program
      (fun x => x=CleanSubbank.bank (s := 9) (bank cs v t u (fun _ => blank) hs))
      (fun x => x=CleanSubbank.bank (s := 9) (bank cs v t u
        (word (destination cs v t u total sv st su)) hs))
      (800*(total+1)+3) :=
  (runs cs v t u hs total sv st su hz hA hsv hv hst ht hsu hu fv ft fu).consequence
    (fun _ h => h) (fun _ h => h)
    (cost_linear v t u hs total sv st su hz hA hsv hv hst ht hsu hu fv ft fu hc)

 theorem outside (cs v t u : List Bool) (total sv st su j : ℕ) (hj : j<total)
    (hv : j<sv ∨ sv+v.length≤j) (ht : j<st ∨ st+t.length≤j)
    (hu : j<su ∨ su+u.length≤j) :
    (destination cs v t u total sv st su).getD j false=cs.getD j false := by
  unfold destination
  rw [ActiveRepairDestinationPatchData.outside _ _ _ j (by simpa [initial] using hj) hu,
      ActiveRepairDestinationPatchData.outside _ _ _ j (by simpa [initial] using hj) ht,
      ActiveRepairDestinationPatchData.outside _ _ _ j (by simpa [initial] using hj) hv]
  simp only [initial,Gather.field,List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using hj)]
  simp

 theorem target_field (cs v t u : List Bool) (total sv st su : ℕ)
    (fv : sv+v.length≤total)
    (hvt : sv+v.length≤st ∨ st+t.length≤sv)
    (hvu : sv+v.length≤su ∨ su+u.length≤sv) :
    Gather.field (destination cs v t u total sv st su) sv v.length=v := by
  unfold destination
  rw [ActiveRepairDestinationPatchData.field_outside _ _ _ sv v.length (by simpa [initial] using fv) hvu,
      ActiveRepairDestinationPatchData.field_outside _ _ _ sv v.length (by simpa [initial] using fv) hvt,
      ActiveRepairDestinationPatchData.field_inside _ _ _ (by simpa [initial] using fv)]

 theorem t_field (cs v t u : List Bool) (total sv st su : ℕ)
    (ft : st+t.length≤total) (htu : st+t.length≤su ∨ su+u.length≤st) :
    Gather.field (destination cs v t u total sv st su) st t.length=t := by
  unfold destination
  rw [ActiveRepairDestinationPatchData.field_outside _ _ _ st t.length (by simpa [initial] using ft) htu,
      ActiveRepairDestinationPatchData.field_inside _ _ _ (by simpa [initial] using ft)]

 theorem u_field (cs v t u : List Bool) (total sv st su : ℕ) (fu : su+u.length≤total) :
    Gather.field (destination cs v t u total sv st su) su u.length=u := by
  unfold destination
  exact ActiveRepairDestinationPatchData.field_inside _ _ _ (by simpa [initial] using fu)

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchRun
