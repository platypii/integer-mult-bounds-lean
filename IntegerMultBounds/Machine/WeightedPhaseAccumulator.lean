import IntegerMultBounds.Machine.UnitPhaseNumerator

/-! A physical two-bit modulo-four accumulator scans literal Boolean controls.
Static weights belong to finite control, and each control is consumed in one
transition. Both flag tapes are literal one-cell words used by the unit kernel. -/
namespace IntegerMultBounds.Machine.WeightedPhaseAccumulator
noncomputable section
open UnitPhaseNumerator (low high flags)
open MarkedWordCleanup (one)

def phaseFin (q : ZMod 4) : Fin 4 := ⟨q.val,by have h := ZMod.val_lt (n := 4) q; exact h⟩
def next (p : Fin 4) (w : ZMod 4) (b : Bool) : Fin 4 := phaseFin ((p.val : ZMod 4)+if b then w else 0)
def decode (sy : Fin 3 → Fin 6) : Fin 4 :=
  ⟨(if sy 0=bitSymbol true then 1 else 0)+(if sy 1=bitSymbol true then 2 else 0),by split_ifs <;> omega⟩
def bank (p : Fin 4) (f : ℤ → Fin 6) (h : ℤ) : Tapes 3 2 := (flags p).append (one f h)

def stepProgram (w : ZMod 4) : Program 3 2 2 where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st=0 then
    let p := next (decode sy) w (decide (sy 2=bitSymbol true))
    some (1,![ (bitSymbol (low p),Move.stay),(bitSymbol (high p),Move.stay),(sy 2,Move.right)])
    else none

theorem decode_bank (p : Fin 4) (f : ℤ → Fin 6) (h : ℤ) : decode (bank p f h).reads=p := by
  change (⟨(if (bitSymbol (low p) : Fin 6)=bitSymbol true then 1 else 0)+
    (if (bitSymbol (high p) : Fin 6)=bitSymbol true then 2 else 0),_⟩ : Fin 4)=p
  apply Fin.ext
  fin_cases p <;> norm_num [low,high,bitSymbol]

theorem step_eq (p : Fin 4) (w : ZMod 4) (b : Bool) (f : ℤ → Fin 6) (h : ℤ) (hb : f h=bitSymbol b) :
    step (stepProgram w) ((bank p f h).start (stepProgram w))=
      some (⟨1,(bank (next p w b) f (h+1)).head,(bank (next p w b) f (h+1)).tape⟩ : Config 3 2 2) := by
  have hr : (bank p f h).reads 2=bitSymbol b := hb
  have hd : decide ((bank p f h).reads 2=bitSymbol true)=b := by
    rw [hr]
    cases b <;> decide
  unfold step
  change (match (stepProgram w).transition 0 (bank p f h).reads with
    | none => none
    | some (st,act) => some (⟨st,fun j => (bank p f h).head j+(act j).2.offset,
        fun j z => if z=(bank p f h).head j then (act j).1 else (bank p f h).tape j z⟩ : Config 3 2 2))=_
  simp only [stepProgram,ite_true,decode_bank,hd]
  congr 1
  apply congrArg₂ (fun head tape => (⟨1,head,tape⟩ : Config 3 2 2))
  · funext j
    fin_cases j
    · change (0 : ℤ)+0=0; omega
    · change (0 : ℤ)+0=0; omega
    · change h+1=h+1; rfl
  · funext j z
    fin_cases j
    · change (if z=0 then bitSymbol (low (next p w b)) else
        (putWord (fun _ => blank) 0 [bitSymbol (low p)]) z)=
        (putWord (fun _ => blank) 0 [bitSymbol (low (next p w b))]) z
      by_cases hz : z=0 <;> simp [putWord,hz]
    · change (if z=0 then bitSymbol (high (next p w b)) else
        (putWord (fun _ => blank) 0 [bitSymbol (high p)]) z)=
        (putWord (fun _ => blank) 0 [bitSymbol (high (next p w b))]) z
      by_cases hz : z=0 <;> simp [putWord,hz]
    · change (if z=h then f h else f z)=f z
      by_cases hz : z=h <;> simp [hz]

theorem step_runs (p : Fin 4) (w : ZMod 4) (b : Bool) (f : ℤ → Fin 6) (h : ℤ) (hb : f h=bitSymbol b) :
    HoareTime (stepProgram w) (fun v => v=bank p f h) (fun v => v=bank (next p w b) f (h+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(bank (next p w b) f (h+1)).head,(bank (next p w b) f (h+1)).tape⟩,le_rfl,?_,?_,rfl⟩
  · rw [run_one,step_eq p w b f h hb]
  · simp [step,stepProgram]

def states : List (ZMod 4) → ℕ
  | [] => 1
  | _::ws => 2+states ws

def program : (ws : List (ZMod 4)) → Program 3 (states ws) 2
  | [] => skip 3 2 (by decide)
  | w::ws => seq (stepProgram w) (program ws)

def accumulate : Fin 4 → List (ZMod 4) → List Bool → Fin 4
  | p,[],_ => p
  | p,w::ws,b::bs => accumulate (next p w b) ws bs
  | p,_::ws,[] => accumulate p ws []

theorem runs (p : Fin 4) (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length)
    (f : ℤ → Fin 6) (h : ℤ) (hb : ∀ j : Fin bs.length,f (h+j.val)=bitSymbol bs[j.val]) :
    HoareTime (program ws) (fun v => v=bank p f h)
      (fun v => v=bank (accumulate p ws bs) f (h+bs.length)) (2*ws.length) := by
  induction ws generalizing p bs h with
  | nil => have he : bs=[] := List.length_eq_zero_iff.mp hl; subst bs; simpa only [program,states,accumulate,List.length_nil,Nat.cast_zero,add_zero] using skip_hoare (by decide : 0<3) (bank p f h)
  | cons w ws ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      have h0 : f h=bitSymbol b := by simpa using hb ⟨0,by simp⟩
      have ht : ∀ j : Fin bs.length,f (h+1+j.val)=bitSymbol bs[j.val] := by
        intro j
        simpa only [List.getElem_cons_succ,Nat.cast_add,Nat.cast_one,add_assoc,add_comm (1 : ℤ)] using hb ⟨j.val+1,by simp⟩
      have hs := (step_runs p w b f h h0).seq (ih (next p w b) bs (by simpa using hl) (h+1) ht)
      exact hs.consequence (fun _ h => h) (fun _ hv => by
        simpa only [accumulate,List.length_cons,Nat.cast_add,Nat.cast_one,add_assoc,add_comm (1 : ℤ)] using hv)
        (by simp; omega)

theorem phaseFin_cast (q : ZMod 4) : ((phaseFin q).val : ZMod 4)=q := by
  simp [phaseFin]

theorem next_cast (p : Fin 4) (w : ZMod 4) (b : Bool) :
    ((next p w b).val : ZMod 4)=(p.val : ZMod 4)+if b then w else 0 := phaseFin_cast _

def weightedSum (ws : List (ZMod 4)) (bs : List Bool) : ZMod 4 :=
  (List.zipWith (fun w b => if b then w else 0) ws bs).sum

theorem accumulate_cast (p : Fin 4) (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length) :
    ((accumulate p ws bs).val : ZMod 4)=(p.val : ZMod 4)+weightedSum ws bs := by
  induction ws generalizing p bs with
  | nil => have he : bs=[] := List.length_eq_zero_iff.mp hl; subst bs; simp [accumulate,weightedSum]
  | cons w ws ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs =>
      rw [accumulate,ih _ _ (by simpa using hl),next_cast]
      simp only [weightedSum,List.zipWith_cons_cons,List.sum_cons]
      ring

/-- An explicit control tape, not a phase-result oracle, is scanned physically. -/
theorem word_runs (p : Fin 4) (ws : List (ZMod 4)) (bs : List Bool) (hl : bs.length=ws.length) :
    HoareTime (program ws)
      (fun v => v=bank p (putWord (fun _ => blank) 0 (bs.map bitSymbol)) 0)
      (fun v => v=bank (accumulate p ws bs) (putWord (fun _ => blank) 0 (bs.map bitSymbol)) bs.length)
      (2*ws.length) := by
  have hr : ∀ j : Fin bs.length, (putWord (fun _ => blank) 0 (bs.map bitSymbol) : ℤ → Fin 6)
      (0+j.val)=bitSymbol bs[j.val] := by
    intro j
    rw [Gather.putWord_getD _ _ _ _ j.isLt,List.getD_eq_getElem _ _ j.isLt]
  simpa only [zero_add] using runs p ws bs hl _ 0 hr

end
end IntegerMultBounds.Machine.WeightedPhaseAccumulator
