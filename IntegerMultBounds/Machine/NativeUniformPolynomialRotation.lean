import IntegerMultBounds.Machine.NativeColumnPhaseFlagsPlaced
import IntegerMultBounds.Machine.UnitPhasePolynomialArray
import IntegerMultBounds.Machine.NativeFixedPhaseFlags

/-! Runtime column-header phase initialization followed by the actual native
coefficient loop. The phase is uniform across the complete polynomial stream;
its two private flags are erased afterwards. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotation
noncomputable section
open MarkedWordCleanup (one)
open SharedPlacementAlphabet (setTape)
open UnitPhasePolynomialLoop (state flagsAt coreBlank)
open DelimitedRadixRecord (Context)

def phase (columns : ℕ) : Fin 4 := ⟨(27*columns)%4,Nat.mod_lt _ (by decide)⟩
def slots : Fin 3 → Fin 64 := ![63,48,49]
theorem slots_injective : Function.Injective slots := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [slots]
def prepare := NativeColumnPhaseFlagsPlaced.program slots slots_injective (by decide : 3+61=64)
def flagged (v : Tapes 60 2) (p : Fin 4) :=
  setTape (setTape v 48 ((UnitPhaseNumerator.flags p).tape 0) 0)
    49 ((UnitPhaseNumerator.flags p).tape 1) 0
def cleared (v : Tapes 60 2) :=
  setTape (setTape v 48 (fun _ => blank) 0) 49 (fun _ => blank) 0
def bank (v : Tapes 60 2) (R columns : ℕ) :=
  (CountedLoopHeaderClean.bank (v.append
    (one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits R)) 1))).append
    (one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns)) 1)
def clearProgram {t : ℕ} (i j : Fin t) : Program t 2 2 where
  tapes_pos := Nat.zero_lt_of_lt i.isLt
  start := 0
  transition := fun st sy => if st=0 then some (1,fun k =>
    (if k=i ∨ k=j then blank else sy k,Move.stay)) else none

def cleanup := clearProgram (48 : Fin 64) 49

def program := seq prepare (seq (extend UnitPhasePolynomialLoop.program 1) cleanup)

def fixedPrepare (p : Fin 4) := Placement.placed (NativeFixedPhaseFlags.triple p)
  (NativeColumnPhaseFlagsPlaced.placement slots slots_injective (by decide : 3+61=64))
def fixedProgram (p : Fin 4) := seq (fixedPrepare p)
  (seq (extend UnitPhasePolynomialLoop.program 1) cleanup)
def negativeProgram := fixedProgram 2

theorem flagged_flags (v : Tapes 60 2) (p : Fin 4) : flagsAt (flagged v p) p := by
  intro i
  fin_cases i <;> simp [flagged,setTape,UnitPhaseNumerator.flags,one,Tapes.append,Fin.addCases]

theorem flagged_core (v : Tapes 60 2) (p : Fin 4) (h : coreBlank v) : coreBlank (flagged v p) := by
  intro i
  have hi : UnitPhaseSharedCoefficient.coreSlots i≠(48 : Fin 60) ∧
      UnitPhaseSharedCoefficient.coreSlots i≠(49 : Fin 60) := by fin_cases i <;> decide
  simpa [flagged,setTape,hi.1,hi.2] using h i

private theorem bank_set (v : Tapes 60 2) (R columns : ℕ) (i : Fin 60)
    (f : ℤ → Fin 6) (p : ℤ) :
    setTape (bank v R columns) (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 i))) f p=
      bank (setTape v i f p) R columns := by
  unfold bank CountedLoopHeaderClean.bank
  rw [SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]

private theorem prepared_bank (v : Tapes 60 2) (R columns : ℕ) :
    NativeColumnPhaseFlagsPlaced.output slots (bank v R columns) (phase columns)=
      bank (flagged v (phase columns)) R columns := by
  change setTape (setTape (bank v R columns)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (48 : Fin 60))))
    ((UnitPhaseNumerator.flags (phase columns)).tape 0) 0)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (49 : Fin 60))))
    ((UnitPhaseNumerator.flags (phase columns)).tape 1) 0 = _
  rw [bank_set,bank_set]
  rfl

private theorem prepare_runs (v : Tapes 60 2) (R columns : ℕ)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank)) :
    HoareTime prepare (fun w => w=bank v R columns)
      (fun w => w=bank (flagged v (phase columns)) R columns) 2 := by
  have h := NativeColumnPhaseFlagsPlaced.runs slots slots_injective (by decide : 3+61=64)
    (bank v R columns) columns ⟨rfl,rfl⟩ (by
      intro i
      fin_cases i <;> first | exact hblank 0 | exact hblank 1)
  change HoareTime prepare (fun w => w=bank v R columns)
    (fun w => w=NativeColumnPhaseFlagsPlaced.output slots (bank v R columns) (phase columns)) 2 at h
  rw [prepared_bank] at h
  exact h

private theorem clear_runs {t : ℕ} (i j : Fin t) (hij : i≠j) (v : Tapes t 2) (p : Fin 4)
    (hf : v.head i=0 ∧ v.tape i=(UnitPhaseNumerator.flags p).tape 0)
    (hg : v.head j=0 ∧ v.tape j=(UnitPhaseNumerator.flags p).tape 1) :
    HoareTime (clearProgram i j) (fun w => w=v)
      (fun w => w=setTape (setTape v i (fun _ => blank) 0) j (fun _ => blank) 0) 1 := by
  rintro w rfl
  let out := setTape (setTape w i (fun _ => blank) 0) j (fun _ => blank) 0
  refine ⟨1,⟨1,out.head,out.tape⟩,le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,clearProgram,Tapes.start,ite_true,Move.offset,add_zero]
    congr 1
    congr 1
    · funext k
      simp only [out,setTape,Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all
    · funext k z
      simp only [out,setTape,Function.update_apply]
      by_cases hki : k=i
      · subst k
        simp only [hf.1,hf.2,ite_true,true_or]
        simp [hij,UnitPhaseNumerator.flags,one,Tapes.append,putWord,Fin.addCases,Function.update_apply]
        exact fun hn he => (hn he).elim
      · by_cases hkj : k=j
        · subst k
          simp [hki,hg.1,hg.2,UnitPhaseNumerator.flags,one,Tapes.append,putWord,Fin.addCases,Function.update_apply]
          exact fun hn he => (hn he).elim
        · simp only [hki,hkj,ite_false,or_self]
          split_ifs <;> simp_all
  · simp [step,clearProgram]

private theorem cleanup_runs (v : Tapes 60 2) (R columns : ℕ) (p : Fin 4)
    (hf : flagsAt v p) :
    HoareTime cleanup (fun w => w=bank v R columns)
      (fun w => w=bank (cleared v) R columns) 1 := by
  have h := clear_runs (48 : Fin 64) 49 (by decide) (bank v R columns) p (hf 0) (hf 1)
  change HoareTime cleanup (fun w => w=bank v R columns)
    (fun w => w=setTape (setTape (bank v R columns)
      (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (48 : Fin 60)))) (fun _ => blank) 0)
      (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (49 : Fin 60)))) (fun _ => blank) 0) 1 at h
  rw [bank_set,bank_set] at h
  exact h

private theorem fixed_prepare_runs (v : Tapes 60 2) (R columns : ℕ) (p : Fin 4)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank)) :
    HoareTime (fixedPrepare p) (fun w => w=bank v R columns)
      (fun w => w=bank (flagged v p) R columns) 1 := by
  let e := NativeColumnPhaseFlagsPlaced.placement slots slots_injective (by decide : 3+61=64)
  have ha : Placement.active e (bank v R columns)=
      (one ((bank v R columns).tape (slots 0)) ((bank v R columns).head (slots 0))).append
      (SharedBank.empty 2 2) := by
    rw [show e=InjectivePlacement.placement slots slots_injective (by decide : 3+61=64) from rfl,
      InjectivePlacement.active_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact (hblank 0).1 | exact (hblank 0).2 |
      exact (hblank 1).1 | exact (hblank 1).2
  have h := Placement.hoare_at (NativeFixedPhaseFlags.triple_runs p
    (one ((bank v R columns).tape (slots 0)) ((bank v R columns).head (slots 0)))) e
    (bank v R columns) ha
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [NativeColumnPhaseFlagsPlaced.replace_output]
  change setTape (setTape (bank v R columns)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (48 : Fin 60))))
    ((UnitPhaseNumerator.flags p).tape 0) 0)
    (Fin.castAdd 1 (Fin.castAdd 2 (Fin.castAdd 1 (49 : Fin 60))))
    ((UnitPhaseNumerator.flags p).tape 1) 0 = _
  rw [bank_set,bank_set]
  rfl

/-- All phase selection comes from the actual runtime columns header. Count
and source are physical loop inputs; the output includes literal flag cleanup. -/
theorem runs (v : Tapes 60 2) (ctx : ℕ → Context 2) (R columns w : ℕ)
    (hw : ∀ i<R,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank))
    (hcore : coreBlank v)
    (hs : v.tape 56=(ctx 0).tape ∧ v.head 56=(ctx 0).start)
    (hnext : ∀ i,i+1<R → (ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime program (fun z => z=bank v R columns)
      (fun z => z=bank (cleared (state (flagged v (phase columns)) ctx (phase columns) R)) R columns)
      (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+40) := by
  have hi := prepare_runs v R columns hblank
  have hl := UnitPhasePolynomialLoop.runs (flagged v (phase columns)) ctx (phase columns) R w hw
    (flagged_flags _ _) (flagged_core _ _ hcore) (by simpa [flagged,setTape] using hs) hnext
  have he := hoare_extend_eq hl
    (one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns)) 1)
  have hc := cleanup_runs (state (flagged v (phase columns)) ctx (phase columns) R) R columns
    (phase columns) (UnitPhasePolynomialLoop.state_flags _ _ _ (flagged_flags _ _) R)
  exact (hi.seq (he.seq hc)).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem fixed_runs (p : Fin 4) (v : Tapes 60 2) (ctx : ℕ → Context 2) (R columns w : ℕ)
    (hw : ∀ i<R,(ctx i).re.length=w ∧ (ctx i).im.length=w)
    (hblank : ∀ i : Fin 2,v.head ⟨48+i.val,by omega⟩=0 ∧
      v.tape ⟨48+i.val,by omega⟩=(fun _ => blank))
    (hcore : coreBlank v)
    (hs : v.tape 56=(ctx 0).tape ∧ v.head 56=(ctx 0).start)
    (hnext : ∀ i,i+1<R → (ctx (i+1)).tape=(ctx i).tape ∧
      (ctx (i+1)).start=(ctx i).start+(ctx i).re.length+(ctx i).im.length+2) :
    HoareTime (fixedProgram p) (fun z => z=bank v R columns)
      (fun z => z=bank (cleared (state (flagged v p) ctx p R)) R columns)
      (R*(24*w+89)+11*(RecursiveChildQuotientsConstant.bits R).length+39) := by
  have hi := fixed_prepare_runs v R columns p hblank
  have hl := UnitPhasePolynomialLoop.runs (flagged v p) ctx p R w hw
    (flagged_flags _ _) (flagged_core _ _ hcore) (by simpa [flagged,setTape] using hs) hnext
  have he := hoare_extend_eq hl
    (one (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits columns)) 1)
  have hc := cleanup_runs (state (flagged v p) ctx p R) R columns p
    (UnitPhasePolynomialLoop.state_flags _ _ _ (flagged_flags _ _) R)
  exact (hi.seq (he.seq hc)).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotation
