import IntegerMultBounds.Machine.GuardTest
import IntegerMultBounds.Machine.CountedLoopReuseAlphabet
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Fixed-control comparison of a runtime-width field and constant, followed
by actual guard-flag append. The original comparison-width header is retained;
the order cell and countdown workspace finish wholly blank at their origins. -/
namespace IntegerMultBounds.Machine.CountedGuardTest
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)
open GuardTest (ordSymbol orderAfter)

def bank (f g flag : ℤ → Fin (a+4)) (px pc pf : ℤ) (ks : List Bool) : Tapes 6 a :=
  ⟨![px,pc,0,pf,0,1],![f,g,fun _ => blank,flag,fun _ => blank,CountedLoopReuseAlphabet.binary ks]⟩

def mark : Program 6 2 a where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s=0 then some (1,fun i =>
    if i=4 then (separator,Move.right) else (sy i,Move.stay)) else none

theorem mark_hoare (v : Tapes 6 a) (ht : v.tape 4=fun _ => blank) (hh : v.head 4=0) :
    HoareTime mark (fun w => w=v)
      (fun w => w=setTape v 4 CountedLoopReuseAlphabet.empty 1) 1 := by
  intro w hw
  subst w
  refine ⟨1,⟨1,(setTape v 4 CountedLoopReuseAlphabet.empty 1).head,
    (setTape v 4 CountedLoopReuseAlphabet.empty 1).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one]
    simp only [step,mark,Tapes.start,ite_true]
    congr 1
    congr 1
    · funext i; fin_cases i <;> simp [setTape,Move.offset,hh]
    · funext i z; fin_cases i <;> simp [setTape,CountedLoopReuseAlphabet.empty,ht,hh] <;> aesop
  · simp [step,mark]

def flagPlace : Fin (2+4) ≃ Fin 6 where
  toFun := ![2,3,0,1,4,5]
  invFun := ![2,3,0,1,4,5]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def compareProgram := CountedLoopReuseAlphabet.program (extend (GuardTest.cmpCell a) 1)
def flagProgram (target : Ordering) := Placement.placed (GuardTest.flagCell target a) flagPlace
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (4 : Fin 6)
def program (target : Ordering) := seq (seq (seq (mark (a := a)) compareProgram) (flagProgram target)) cleanup

def columns (f g F : ℤ → Fin (a+4)) (px pc pf : ℤ) (xs ys : List Bool)
    (start i : ℕ) : Tapes 4 a :=
  (GuardTest.bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
    (Function.update (fun _ => blank) 0 (ordSymbol (orderAfter .eq xs ys start i)))
    (px+start+i) (pc+i) 0).append (⟨fun _ => pf,fun _ => F⟩ : Tapes 1 a)

theorem column_hoare (f g F : ℤ → Fin (a+4)) (px pc pf : ℤ) (xs ys : List Bool)
    (start d i : ℕ) (hx : start+d ≤ xs.length) (hy : d ≤ ys.length) (hi : i<d) :
    HoareTime (extend (GuardTest.cmpCell a) 1)
      (fun w => w=columns f g F px pc pf xs ys start i)
      (fun w => w=columns f g F px pc pf xs ys start (i+1)) 1 := by
  have h := GuardTest.cmpCell_hoare (putWord f px (xs.map bitSymbol))
    (putWord g pc (ys.map bitSymbol))
    (Function.update (fun _ => blank) 0 (ordSymbol (orderAfter .eq xs ys start i)))
    (px+start+i) (pc+i) 0 (xs.getD (start+i) false) (ys.getD i false)
    (orderAfter .eq xs ys start i)
    (by rw [show px+(start : ℤ)+i=px+((start+i : ℕ) : ℤ) by omega,Gather.putWord_getD _ _ _ _ (by omega)])
    (by rw [Gather.putWord_getD _ _ _ _ (by omega)]) (by simp)
  have h' := hoare_extend_eq h (⟨fun _ => pf,fun _ => F⟩ : Tapes 1 a)
  refine h'.consequence (fun _ h => h) (fun _ h => ?_) le_rfl
  rw [h,Function.update_idem,← GuardTest.orderAfter_succ]
  apply congrArg₂ Tapes.mk
  · funext j; fin_cases j <;> simp [GuardTest.bank,Fin.addCases] <;> omega
  · rfl

/-- Compare exactly d physical bits using the retained original count word,
append the requested order flag and physically clear all private controls.
Both compared tapes advance exactly d cells; the flag head advances one. -/
theorem runs (target : Ordering) (f g F : ℤ → Fin (a+4)) (px pc pf : ℤ)
    (xs ys : List Bool) (start d : ℕ) (ks : List Bool)
    (hk : Counter.value ks=d) (_ck : GrowingCounterData.Canonical ks)
    (hx : start+d ≤ xs.length) (hy : d ≤ ys.length) :
    HoareTime (program target)
      (fun w => w=bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        F (px+start) pc pf ks)
      (fun w => w=bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        (Function.update F pf (bitSymbol (decide (orderAfter .eq xs ys start d=target))))
        (px+start+d) (pc+d) (pf+1) ks)
      (7*d+7*ks.length+25) := by
  let I := bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol)) F (px+start) pc pf ks
  let A := CountedLoopReuseAlphabet.bank (columns f g F px pc pf xs ys start d)
    CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ks) 1 1
  have hm := mark_hoare I rfl rfl
  have hmi : setTape I 4 CountedLoopReuseAlphabet.empty 1 =
      CountedLoopReuseAlphabet.bank (columns f g F px pc pf xs ys start 0)
        CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary ks) 1 1 := by
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> first | rfl | (change px+start=px+start+0; omega) | (change pc=pc+0; omega)
    · funext i z; fin_cases i <;> first | rfl | (change blank=(Function.update (fun _ : ℤ => (blank : Fin (a+4))) 0 blank) z; simp)
  rw [hmi] at hm
  have hc := CountedLoopReuseAlphabet.loop_hoare (extend (GuardTest.cmpCell a) 1) ks d
    (columns f g F px pc pf xs ys start) (fun _ => 1) hk
    (fun i hi => column_hoare f g F px pc pf xs ys start d i hx hy hi)
  have hi : Placement.active flagPlace A=GuardTest.bank2
      (Function.update (fun _ => blank) 0 (ordSymbol (orderAfter .eq xs ys start d))) F 0 pf := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have hf := Placement.hoare_at (GuardTest.flagCell_hoare target (fun _ => blank) F 0 pf
    (orderAfter .eq xs ys start d)) flagPlace A hi
  let B0 := setTape (bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
    (Function.update F pf (bitSymbol (decide (orderAfter .eq xs ys start d=target))))
    (px+start+d) (pc+d) (pf+1) ks) 4 CountedLoopReuseAlphabet.empty 1
  have hf' : HoareTime (flagProgram target) (fun w => w=A) (fun w => w=B0) 1 := by
    refine hf.consequence (fun _ h => h) ?_ le_rfl
    rintro w ⟨z,rfl,rfl⟩
    apply congrArg₂ Tapes.mk
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;> first | rfl | simp [bank,GuardTest.bank2,flagPlace,Tapes.append,Fin.addCases]
  have he := BinaryDescriptorCleanupList.one_hoare (4 : Fin 6) B0 [] rfl rfl
  have heout : setTape B0 4 (fun _ => blank) 0 = bank
      (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
      (Function.update F pf (bitSymbol (decide (orderAfter .eq xs ys start d=target))))
      (px+start+d) (pc+d) (pf+1) ks := by
    dsimp only [B0]
    rw [SharedPlacementAlphabet.setTape_setTape]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [heout] at he
  exact (((hm.seq hc).seq hf').seq he).consequence (fun _ h => h) (fun _ h => h)
    (by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,List.length_nil]; omega)

/-- Canonical descriptor length is paid by the compared physical width. -/
theorem cost_linear (d : ℕ) (ks : List Bool) (hk : Counter.value ks=d)
    (ck : GrowingCounterData.Canonical ks) : 7*d+7*ks.length+25 ≤ 14*d+32 := by
  have hl := GrowingCounterData.canonical_width ks ck
  rw [hk] at hl
  have hn := Nat.log2_le_self d
  omega

theorem runs_linear (target : Ordering) (f g F : ℤ → Fin (a+4)) (px pc pf : ℤ)
    (xs ys : List Bool) (start d : ℕ) (ks : List Bool)
    (hk : Counter.value ks=d) (ck : GrowingCounterData.Canonical ks)
    (hx : start+d ≤ xs.length) (hy : d ≤ ys.length) :
    HoareTime (program target)
      (fun w => w=bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        F (px+start) pc pf ks)
      (fun w => w=bank (putWord f px (xs.map bitSymbol)) (putWord g pc (ys.map bitSymbol))
        (Function.update F pf (bitSymbol (decide (orderAfter .eq xs ys start d=target))))
        (px+start+d) (pc+d) (pf+1) ks) (14*d+32) :=
  (runs target f g F px pc pf xs ys start d ks hk ck hx hy).consequence
    (fun _ h => h) (fun _ h => h) (cost_linear d ks hk ck)

/-- Both private tapes are wholly blank at head zero at either clean boundary. -/
theorem bank_private (f g F : ℤ → Fin (a+4)) (px pc pf : ℤ) (ks : List Bool) :
    (bank f g F px pc pf ks).head 2=0 ∧ (bank f g F px pc pf ks).tape 2=(fun _ => blank) ∧
    (bank f g F px pc pf ks).head 4=0 ∧ (bank f g F px pc pf ks).tape 4=fun _ => blank :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem bank_header (f g F : ℤ → Fin (a+4)) (px pc pf : ℤ) (ks : List Bool) :
    (bank f g F px pc pf ks).head 5=1 ∧
      (bank f g F px pc pf ks).tape 5=CountedLoopReuseAlphabet.binary ks := ⟨rfl,rfl⟩

end
end IntegerMultBounds.Machine.CountedGuardTest
