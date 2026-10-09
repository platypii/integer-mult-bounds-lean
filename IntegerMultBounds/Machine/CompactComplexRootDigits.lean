import IntegerMultBounds.Machine.CompactComplexRootDigitRound
import IntegerMultBounds.Machine.BinaryDescriptorQueueEmit
import IntegerMultBounds.Machine.LoopChain
import Mathlib.Data.Nat.Digits.Lemmas

/-! A fixed while controller physically enumerates all low-to-high base digits
of the original active-prefix word, writing a forward binary-field queue.
Neither the digits nor root-path descriptors enter its finite control. -/
namespace IntegerMultBounds.Machine.CompactComplexRootDigits
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
open ActiveRepairRankHeadersCommands (bank)
variable {a : ℕ}

def state (remaining : ℕ) : ActiveRepairRankHeadersCommands.State :=
  fun i => if i=0 then some remaining else none

def input (remaining : ℕ) (f : ℤ → Fin (a+4)) (p : ℤ) : Tapes 44 a :=
  (bank (state remaining)).append (FiniteReturnStack.bank f p)

def fields (ds : List ℕ) : List (Fin (a+4)) :=
  ds.flatMap (fun d => (bits d).map bitSymbol++[separator])

def emitFocus : Fin 2 → Fin 44 := ![4,43]
theorem emit_injective : Function.Injective emitFocus := by decide
def emitPlacement := InjectivePlacement.placement emitFocus emit_injective (by decide : 2+(44-2)=44)
def emitProgram := Placement.placed (BinaryDescriptorQueueEmit.program (a := a)) emitPlacement

def body (base : ℕ) : Σ q, Program 44 q a :=
  ⟨_,seq (extend (CompactChildHeadersArithmetic.compile (a := a)
    (CompactComplexRootDigitRound.schedule base)).2 1) emitProgram⟩

def test (sy : Fin 44 → Fin (a+4)) : Bool := decide (sy 0 ≠ blank)
def program (base : ℕ) := whileLoop (body (a := a) base).2 test

private theorem emit_active (remaining base : ℕ) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.active emitPlacement
      ((bank (CompactComplexRootDigitRound.finished (state remaining) remaining base)).append
        (FiniteReturnStack.bank f p)) = Copy.tapes (BinaryDescriptorStack.descriptor (bits (remaining%base))) f 1 p := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [emitPlacement,InjectivePlacement.active_slot]
  all_goals fin_cases i
  all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded (bits (remaining%base))).symm

private theorem emit_output (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) :
    Copy.tapes (fun _ => blank) (putWord f p (xs.map bitSymbol++[separator])) 0 (p+xs.length+1) =
      setTape (setTape (Copy.tapes (BinaryDescriptorStack.descriptor xs) f 1 p)
        0 (fun _ => blank) 0) 1 (putWord f p (xs.map bitSymbol++[separator])) (p+xs.length+1) := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem replace_write {s u t : ℕ} (e : Fin (s+u) ≃ Fin t) (v : Tapes t a)
    (small : Tapes s a) (i : Fin s) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace e v (setTape small i f p)=
      setTape (Placement.replace e v small) (e (Fin.castAdd u i)) f p := by
  have h : Placement.replace e v (setTape small i f p)=
      Placement.replace e (Placement.replace e v small)
        (setTape (Placement.active e (Placement.replace e v small)) i f p) := by
    simp only [Placement.active_replace]
    unfold Placement.replace
    rw [Placement.extra_combine]
  rw [h,PlacedDescriptorConstruction.replace_setTape]

private theorem setTape_append_right {l r : ℕ} (v : Tapes l a) (w : Tapes r a) (i : Fin r)
    (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append w) (Fin.natAdd l i) f p=v.append (setTape w i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem cleared_state (remaining base : ℕ) :
    Function.update (CompactComplexRootDigitRound.finished (state remaining) remaining base) 4 none=
      state (remaining/base) := by
  funext i
  by_cases h0 : i=0
  · subst i; simp [state,CompactComplexRootDigitRound.finished,ActiveRepairRankHeadersCommands.put,Function.update]
  by_cases h4 : i=4
  · subst i; simp [state,Function.update]
  simp [state,CompactComplexRootDigitRound.finished,ActiveRepairRankHeadersCommands.put,Function.update,h0,h4]

private theorem emit_replace (remaining base : ℕ) (f : ℤ → Fin (a+4)) (p : ℤ) :
    Placement.replace emitPlacement
      ((bank (CompactComplexRootDigitRound.finished (state remaining) remaining base)).append
        (FiniteReturnStack.bank f p))
      (Copy.tapes (fun _ => blank) (putWord f p ((bits (remaining%base)).map bitSymbol++[separator]))
        0 (p+(bits (remaining%base)).length+1)) =
      input (remaining/base) (putWord f p ((bits (remaining%base)).map bitSymbol++[separator]))
        (p+(bits (remaining%base)).length+1) := by
  rw [emit_output,← emit_active remaining base f p,
    replace_write,PlacedDescriptorConstruction.replace_setTape]
  simp only [emitPlacement,InjectivePlacement.active_slot,emitFocus]
  change setTape (setTape _ (Fin.castAdd 1 (Fin.castAdd 15 (4 : Fin 28))) (fun _ => blank) 0)
    (Fin.natAdd 43 (0 : Fin 1)) _ _ = _
  rw [SharedPlacementAlphabet.setTape_append_left,setTape_append_right]
  unfold bank CleanSubbank.bank
  rw [SharedPlacementAlphabet.setTape_append_left,← ActiveRepairRankHeadersCommands.erase_caller,cleared_state]
  apply congrArg (fun tail => (bank (a := a) (state (remaining/base))).append tail)
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def bodyCost (base remaining : ℕ) :=
  CompactChildHeadersArithmetic.scheduleCost (CompactComplexRootDigitRound.schedule base) (state remaining)+
    2*(bits (remaining%base)).length+6

theorem body_runs (base remaining : ℕ) (hb : 0 < base) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (body (a := a) base).2 (fun x => x=input remaining f p)
      (fun x => x=input (remaining/base)
        (putWord f p ((bits (remaining%base)).map bitSymbol++[separator]))
        (p+(bits (remaining%base)).length+1)) (bodyCost base remaining) := by
  have hr := CompactComplexRootDigitRound.runs_framed base remaining hb (state remaining)
    (by simp [state]) (by simp [state]) (by simp [state]) (by simp [state])
    (by simp [state]) (by simp [state]) (FiniteReturnStack.bank (a := a) f p)
  have he := Placement.hoare_at (BinaryDescriptorQueueEmit.runs (a := a) f p (bits (remaining%base)))
    emitPlacement _ (emit_active remaining base f p)
  have he' : HoareTime emitProgram
      (fun x => x=(bank (CompactComplexRootDigitRound.finished (state remaining) remaining base)).append
        (FiniteReturnStack.bank f p))
      (fun x => x=input (remaining/base)
        (putWord f p ((bits (remaining%base)).map bitSymbol++[separator]))
        (p+(bits (remaining%base)).length+1)) (2*(bits (remaining%base)).length+5) := by
    apply he.consequence (fun _ h => h) _ le_rfl
    rintro x ⟨y,rfl,rfl⟩
    exact emit_replace remaining base f p
  exact (hr.seq he').consequence (fun _ h => h) (fun _ h => h) (by simp [bodyCost]; omega)


private theorem bits_nil_iff (n : ℕ) : bits n=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := RecursiveChildQuotientsConstant.bits_value n
    rw [h] at hv
    exact hv.symm
  · rintro rfl; rfl

private theorem descriptor_head_blank (xs : List Bool) :
    BinaryDescriptorStack.descriptor (a := a) xs 1=blank ↔ xs=[] := by
  cases xs with
  | nil => simp [BinaryDescriptorStack.descriptor,BinaryDescriptorStack.empty,putWord]
  | cons b bs =>
    rw [BinaryDescriptorStack.descriptor,List.map_cons,putWord_head]
    cases b <;> simp [bitSymbol,blank,Fin.ext_iff]

theorem test_input (remaining : ℕ) (f : ℤ → Fin (a+4)) (p : ℤ) :
    test (input remaining f p).reads=decide (remaining≠0) := by
  have hr : (input remaining f p).reads 0=RadixZeroFill.encodedBinary (bits remaining) 1 := rfl
  unfold test
  rw [hr,← BinaryDescriptorStackRoundtrip.descriptor_encoded]
  simp only [ne_eq,descriptor_head_blank,bits_nil_iff]

def loopCost (base remaining : ℕ) : ℕ :=
  if h : 1 < base ∧ 0 < remaining then bodyCost base remaining+2+loopCost base (remaining/base) else 0
termination_by remaining
decreasing_by exact Nat.div_lt_self h.2 h.1

private theorem loopCost_zero (base : ℕ) : loopCost base 0=0 := by
  rw [loopCost]
  simp only [dite_eq_right (show ¬(1 < base ∧ 0 < 0) by omega)]

private theorem loopCost_step (base remaining : ℕ) (hb : 1 < base) (hn : 0 < remaining) :
    loopCost base remaining=bodyCost base remaining+2+loopCost base (remaining/base) := by
  rw [loopCost]
  simp only [dite_eq_left (And.intro hb hn)]

/-- The physical loop outputs exactly the original number's low-to-high digits
and halts with its remaining-prefix descriptor equal to canonical zero. -/
theorem runs (base remaining : ℕ) (hb : 1 < base) (f : ℤ → Fin (a+4)) (p : ℤ) :
    HoareTime (program (a := a) base) (fun v => v=input remaining f p)
      (fun v => v=input 0 (putWord f p (fields (Nat.digits base remaining)))
        (p+(fields (a := a) (Nat.digits base remaining)).length)) (loopCost base remaining) := by
  induction remaining using Nat.strong_induction_on generalizing f p with
  | h remaining ih =>
    by_cases hn : remaining=0
    · subst remaining
      simpa only [Nat.digits_zero,fields,List.flatMap_nil,putWord,List.length_nil,Nat.cast_zero,add_zero,
        loopCost_zero,program,Finset.range_zero,Finset.sum_empty] using
        (while_chain_hoare (body (a := a) base).2 test (fun _ => input (a := a) 0 f p)
          (fun _ => 0) 0 (by intro j hj; omega) (by intro j hj; omega)
          (by rw [test_input]; simp))
    · have hpos : 0 < remaining := by omega
      have hq : remaining/base < remaining := Nat.div_lt_self hpos hb
      let chunk : List (Fin (a+4)) := (bits (remaining%base)).map bitSymbol++[separator]
      have hchunk : chunk.length=(bits (remaining%base)).length+1 := by simp [chunk]
      let f' := putWord f p chunk
      let p' := p+chunk.length
      have hbody := body_runs (a := a) base remaining (by omega) f p
      have hbody' : HoareTime (body (a := a) base).2 (fun v => v=input remaining f p)
          (fun v => v=input (remaining/base) f' p') (bodyCost base remaining) := by
        simpa [f',p',chunk,hchunk,Nat.cast_add,Nat.cast_one,add_assoc] using hbody
      rintro v rfl
      obtain ⟨k,c,hk,hr,hh,hout⟩ := hbody' (input remaining f p) rfl
      obtain ⟨k',c',hk',hr',hh',hout'⟩ := ih (remaining/base) hq f' p'
        (input (remaining/base) f' p') rfl
      have hi := while_run_iteration (body (a := a) base).2 test (input remaining f p)
        (by rw [test_input]; simp [hn]) hr hh
      rw [hout] at hi
      refine ⟨k+2+k',c',?_,?_,hh',?_⟩
      · rw [loopCost_step base remaining hb hpos]
        omega
      · rw [program,run_add,hi]
        exact hr'
      · rw [hout']
        rw [Nat.digits_eq_cons_digits_div hb hn]
        simp only [fields,List.flatMap_cons]
        rw [putWord_append_forward]
        simp [p',chunk,List.length_append,List.length_map,Nat.cast_add,Nat.cast_one,
          add_assoc,add_comm,add_left_comm]


private theorem bodyCost_le (base remaining : ℕ) :
    bodyCost base remaining ≤ 100100*(remaining+base+1)^2 := by
  have hr := CompactComplexRootDigitRound.cost_le base remaining (state remaining) (by simp [state])
  have hl := ActiveRepairRankHeadersCommands.bits_length (remaining%base)
  have hm : remaining%base ≤ remaining := Nat.mod_le _ _
  have hp : 0 < remaining+base+1 := by omega
  have hs : remaining+base+1 ≤ (remaining+base+1)^2 := by
    simpa only [pow_two] using Nat.le_mul_of_pos_left (remaining+base+1) hp
  unfold bodyCost
  nlinarith

/-- A descriptor-polynomial bound times the logarithmic number of generated
base digits; every loop test and return transition is counted. -/
theorem cost_le (base remaining : ℕ) (hb : 1 < base) :
    loopCost base remaining ≤ 101000*(remaining+base+1)^2*(Nat.digits base remaining).length := by
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    by_cases hn : remaining=0
    · subst remaining; simp only [loopCost_zero,Nat.digits_zero,List.length_nil,Nat.mul_zero,Nat.le_refl]
    · have hpos : 0 < remaining := by omega
      have hq : remaining/base < remaining := Nat.div_lt_self hpos hb
      have htail := ih (remaining/base) hq
      have hB : remaining/base+base+1 ≤ remaining+base+1 := by
        have h := Nat.div_le_self remaining base
        omega
      have hsq := Nat.mul_le_mul hB hB
      have hm := Nat.mul_le_mul_right (Nat.digits base (remaining/base)).length
        (Nat.mul_le_mul_left 101000 hsq)
      simp only [← pow_two] at hm
      have htail' := htail.trans hm
      have hbody : bodyCost base remaining+2 ≤ 101000*(remaining+base+1)^2 := by
        have h := bodyCost_le base remaining
        nlinarith
      rw [loopCost_step base remaining hb hpos,Nat.digits_eq_cons_digits_div hb hn,List.length_cons]
      calc
        bodyCost base remaining+2+loopCost base (remaining/base) ≤
            101000*(remaining+base+1)^2+
              101000*(remaining+base+1)^2*(Nat.digits base (remaining/base)).length :=
          Nat.add_le_add hbody htail'
        _ = 101000*(remaining+base+1)^2*((Nat.digits base (remaining/base)).length+1) := by
          rw [Nat.mul_add,Nat.mul_one]
          omega

/-- A complete native stage bank remains a stationary frame through the root
enumerator; the queue and all controller state are on appended tapes. -/
theorem runs_framed {t : ℕ} (base remaining : ℕ) (hb : 1 < base)
    (f : ℤ → Fin (a+4)) (p : ℤ) (native : Tapes t a) :
    HoareTime (extend (program (a := a) base) t)
      (fun v => v=(input remaining f p).append native)
      (fun v => v=(input 0 (putWord f p (fields (Nat.digits base remaining)))
        (p+(fields (a := a) (Nat.digits base remaining)).length)).append native)
      (101000*(remaining+base+1)^2*(Nat.digits base remaining).length) := by
  have h := hoare_extend_eq (runs base remaining hb f p) native
  exact h.consequence (fun _ h => h) (fun _ h => h) (cost_le base remaining hb)

end
end IntegerMultBounds.Machine.CompactComplexRootDigits
