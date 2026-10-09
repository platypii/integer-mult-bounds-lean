import IntegerMultBounds.Machine.CountedGuardGadgetRecord

/-! One fixed pair of counted loops generates exactly the legacy three-flag
word for every record. The original record-count descriptor is retained. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetArray
noncomputable section
variable {a : ℕ}
open CountedGuardGadgetRecord (bank word)
open SharedPlacementAlphabet

def stateV (q : ℕ) (V W C1 C2 C3 : List Bool) (ds bs : List Bool) (i : ℕ) : Tapes 11 a :=
  bank V W C1 C2 C3 (word (GuardGadget.flagWordV q V C1 C2 i)) (i*q : ℕ) 0 0 0 0 (2*i : ℕ) ds bs

def stateW (q b n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs : List Bool) (i : ℕ) : Tapes 11 a :=
  bank V W C1 C2 C3 (word (GuardGadget.flagWordW q b n V W C1 C2 C3 i))
    (n*q : ℕ) (i*b : ℕ) 0 0 0 (2*n+i : ℕ) ds bs

theorem append_bit (xs : List Bool) (b : Bool) :
    Function.update (word (a := a) xs) xs.length (bitSymbol b) = word (xs++[b]) := by
  unfold word
  rw [List.map_append]
  simpa only [List.map_singleton,List.length_map,zero_add] using
    Gather.putWord_snoc (fun _ => blank) 0 (xs.map (bitSymbol (a := a))) (bitSymbol b)

theorem recordV (q n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs : List Bool)
    (hq : 1 ≤ q) (hd : Counter.value ds=q-1) (cd : GrowingCounterData.Canonical ds)
    (hV : V.length=n*q) (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (i : ℕ) (hi : i<n) :
    HoareTime (CountedGuardGadgetRecord.digitV (a := a))
      (fun v => v=stateV q V W C1 C2 C3 ds bs i)
      (fun v => v=stateV q V W C1 C2 C3 ds bs (i+1)) (44*q+104) := by
  let F := GuardGadget.flagWordV q V C1 C2 i
  let x := decide (GuardTest.orderAfter .eq V C1 (i*q+1) (q-1)=.lt)
  let y := decide (GuardTest.orderAfter .eq V C2 (i*q+1) (q-1)=.gt)
  have hlen : F.length=2*i := GuardGadget.flagWordV_length q V C1 C2 i
  have h := CountedGuardGadgetRecord.digitV_hoare V W C1 C2 C3 (word (a := a) F) 0 (2*i : ℕ) ds bs (i*q) q hq hd cd
    (by rw [hV,show i*q+q=(i+1)*q by ring]; exact Nat.mul_le_mul_right q (by omega)) hc1 hc2
  have e1 : Function.update (word (a := a) F) (2*i : ℕ) (bitSymbol x)=word (F++[x]) := by
    rw [← hlen]; exact append_bit F x
  have e2 : Function.update (word (a := a) (F++[x])) ((2*i : ℕ)+1 : ℤ) (bitSymbol y)=word (F++[x,y]) := by
    have hl : (F++[x]).length=2*i+1 := by simp [hlen]
    rw [show ((2*i : ℕ) : ℤ)+1=((2*i+1 : ℕ) : ℤ) by push_cast; omega,← hl,append_bit]
    simp [List.append_assoc]
  change HoareTime _ _ (fun v => v=bank V W C1 C2 C3
    (Function.update (Function.update (word F) (2*i : ℕ) (bitSymbol x)) ((2*i : ℕ)+1) (bitSymbol y))
    (i*q+q : ℕ) 0 0 0 0 ((2*i : ℕ)+2) ds bs) _ at h
  rw [e1,e2] at h
  have ew : F++[x,y]=GuardGadget.flagWordV q V C1 C2 (i+1) := rfl
  rw [ew,show i*q+q=(i+1)*q by ring,
    show ((2*i : ℕ) : ℤ)+2=((2*(i+1) : ℕ) : ℤ) by push_cast; ring] at h
  exact h

theorem recordW (q b n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs : List Bool)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hW : W.length=n*b) (hc3 : C3.length=b) (i : ℕ) (hi : i<n) :
    HoareTime (CountedGuardGadgetRecord.digitW (a := a))
      (fun v => v=stateW q b n V W C1 C2 C3 ds bs i)
      (fun v => v=stateW q b n V W C1 C2 C3 ds bs (i+1)) (15*b+35) := by
  let F := GuardGadget.flagWordW q b n V W C1 C2 C3 i
  let x := decide (GuardTest.orderAfter .eq W C3 (i*b) b=.gt)
  have hlen : F.length=2*n+i := GuardGadget.flagWordW_length q b n V W C1 C2 C3 i
  have h := CountedGuardGadgetRecord.digitW_hoare V W C1 C2 C3 (word (a := a) F) (n*q : ℕ) (2*n+i : ℕ) ds bs (i*b) b hb cb
    (by rw [hW,show i*b+b=(i+1)*b by ring]; exact Nat.mul_le_mul_right b (by omega)) hc3
  have e1 : Function.update (word (a := a) F) (2*n+i : ℕ) (bitSymbol x)=word (F++[x]) := by
    rw [← hlen]; exact append_bit F x
  change HoareTime _ _ (fun v => v=bank V W C1 C2 C3
    (Function.update (word F) (2*n+i : ℕ) (bitSymbol x)) (n*q : ℕ) (i*b+b : ℕ) 0 0 0 ((2*n+i : ℕ)+1) ds bs) _ at h
  rw [e1,show F++[x]=GuardGadget.flagWordW q b n V W C1 C2 C3 (i+1) from rfl,
    show i*b+b=(i+1)*b by ring,
    show ((2*n+i : ℕ) : ℤ)+1=((2*n+(i+1) : ℕ) : ℤ) by push_cast; ring] at h
  exact h

def marked (v : Tapes 11 a) (ns : List Bool) : Tapes 13 a :=
  CountedLoopReuseAlphabet.bank v CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ns) 1 1

def loopV := CountedLoopReuseAlphabet.program (CountedGuardGadgetRecord.digitV (a := a))
def loopW := CountedLoopReuseAlphabet.program (CountedGuardGadgetRecord.digitW (a := a))
def loops := seq (loopV (a := a)) loopW

theorem loops_hoare (q b n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs ns : List Bool)
    (hq : 1 ≤ q) (hd : Counter.value ds=q-1) (cd : GrowingCounterData.Canonical ds)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hn : Counter.value ns=n)
    (hV : V.length=n*q) (hW : W.length=n*b)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b) :
    HoareTime (loops (a := a))
      (fun v => v=marked (stateV q V W C1 C2 C3 ds bs 0) ns)
      (fun v => v=marked (stateW q b n V W C1 C2 C3 ds bs n) ns)
      (n*(44*q+15*b+151)+14*ns.length+33) := by
  have hv := CountedLoopReuseAlphabet.loop_hoare (CountedGuardGadgetRecord.digitV (a := a)) ns n
    (stateV q V W C1 C2 C3 ds bs) (fun _ => 44*q+104) hn
    (fun i hi => recordV q n V W C1 C2 C3 ds bs hq hd cd hV hc1 hc2 i hi)
  have hw := CountedLoopReuseAlphabet.loop_hoare (CountedGuardGadgetRecord.digitW (a := a)) ns n
    (stateW q b n V W C1 C2 C3 ds bs) (fun _ => 15*b+35) hn
    (fun i hi => recordW q b n V W C1 C2 C3 ds bs hb cb hW hc3 i hi)
  have he : stateW (a := a) q b n V W C1 C2 C3 ds bs 0=stateV q V W C1 C2 C3 ds bs n := by
    simp only [stateW,stateV,GuardGadget.flagWordW,Nat.zero_mul,Nat.add_zero,Nat.cast_zero]
  rw [he] at hw
  exact (hv.seq hw).consequence (fun _ h => h) (fun _ h => h) (by
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
    simp only [Nat.mul_add]
    omega)

def input (v : Tapes 11 a) (ns : List Bool) : Tapes 13 a :=
  CountedLoopReuseAlphabet.bank v (fun _ => blank) (CountedLoopReuseAlphabet.binary ns) 0 1

def mark : Program 13 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s=0 then some (1,fun i =>
    if i=11 then (separator,Move.right) else (sy i,Move.stay)) else none

theorem marks (v : Tapes 11 a) (ns : List Bool) :
    HoareTime (mark (a := a)) (fun w => w=input v ns) (fun w => w=marked v ns) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(marked v ns).head,(marked v ns).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,mark,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [input,marked,CountedLoopReuseAlphabet.bank,
        CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases,Move.offset]
    · funext i z; fin_cases i <;> simp [input,marked,CountedLoopReuseAlphabet.bank,
        CountedLoopReuseAlphabet.controls,Tapes.append,Fin.addCases,CountedLoopReuseAlphabet.empty] <;> aesop
  · simp [step,mark]

def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (11 : Fin 13)
def program := seq (seq (mark (a := a)) loops) cleanup

theorem runs (q b n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs ns : List Bool)
    (hq : 1 ≤ q) (hd : Counter.value ds=q-1) (cd : GrowingCounterData.Canonical ds)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs) (hn : Counter.value ns=n)
    (hV : V.length=n*q) (hW : W.length=n*b)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b) :
    HoareTime (program (a := a))
      (fun v => v=input (stateV q V W C1 C2 C3 ds bs 0) ns)
      (fun v => v=input (stateW q b n V W C1 C2 C3 ds bs n) ns)
      (n*(44*q+15*b+151)+14*ns.length+40) := by
  have hm := marks (stateV (a := a) q V W C1 C2 C3 ds bs 0) ns
  have hl := loops_hoare (a := a) q b n V W C1 C2 C3 ds bs ns hq hd cd hb cb hn hV hW hc1 hc2 hc3
  have he := BinaryDescriptorCleanupList.one_hoare (11 : Fin 13)
    (marked (stateW (a := a) q b n V W C1 C2 C3 ds bs n) ns) [] rfl rfl
  have e : setTape (marked (stateW (a := a) q b n V W C1 C2 C3 ds bs n) ns) 11 (fun _ => blank) 0 =
      input (stateW q b n V W C1 C2 C3 ds bs n) ns := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [e] at he
  exact ((hm.seq hl).seq he).consequence (fun _ h => h) (fun _ h => h) (by simp; omega)

theorem runs_linear (q b n : ℕ) (V W C1 C2 C3 : List Bool) (ds bs ns : List Bool)
    (hq : 1 ≤ q) (hd : Counter.value ds=q-1) (cd : GrowingCounterData.Canonical ds)
    (hb : Counter.value bs=b) (cb : GrowingCounterData.Canonical bs)
    (hn : Counter.value ns=n) (cn : GrowingCounterData.Canonical ns)
    (hV : V.length=n*q) (hW : W.length=n*b)
    (hc1 : C1.length=q-1) (hc2 : C2.length=q-1) (hc3 : C3.length=b) :
    HoareTime (program (a := a))
      (fun v => v=input (stateV q V W C1 C2 C3 ds bs 0) ns)
      (fun v => v=input (stateW q b n V W C1 C2 C3 ds bs n) ns)
      (n*(44*q+15*b+165)+54) := by
  have hl := GrowingCounterData.canonical_width ns cn
  rw [hn] at hl
  have hh := Nat.log2_le_self n
  exact (runs q b n V W C1 C2 C3 ds bs ns hq hd cd hb cb hn hV hW hc1 hc2 hc3).consequence
    (fun _ h => h) (fun _ h => h) (by simp only [Nat.mul_add]; omega)

end
end IntegerMultBounds.Machine.CountedGuardGadgetArray
