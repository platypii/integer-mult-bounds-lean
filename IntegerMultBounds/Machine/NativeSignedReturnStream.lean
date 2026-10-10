import IntegerMultBounds.Machine.RadixSignedShiftRight
import IntegerMultBounds.Machine.DelimitedRadixRecord
import IntegerMultBounds.Machine.CountedBankHeaderClean
import IntegerMultBounds.Machine.SignedRadixExactReturn

/-! One fixed native streaming transducer shifts each nonempty signed field,
retains both field separators, and pays source/output rewind and old-source
erasure. No per-record arithmetic controls are supplied by the caller. -/
namespace IntegerMultBounds.Machine.NativeSignedReturnStream
open RadixDigits
open RadixSignedShiftRight (Word shifted track cfg tapes)

def program : Program 2 4 2 where
  tapes_pos := by decide
  start := 0
  transition := fun state sy =>
    if state=3 then some (0,fun i => if i=0 then (sy i,.right) else (separator,.right))
    else if state=0 then
      match readDigit (sy 0) with
      | none => none
      | some digit => some (track digit,fun i => (sy i,if i=0 then .right else .stay))
    else match readDigit (sy 0) with
      | some digit => some (track digit,fun i => if i=0 then (sy i,.right) else (digitSymbol digit,.right))
      | none => some (3,fun i => if i=0 then (sy i,.stay) else
          (digitSymbol (if state=2 then 1 else 0),.right))

theorem digit_step (x last : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ)
    (hx : f p=digitSymbol x) :
    step program (cfg f g p q (track last)) =
      some (cfg f (Function.update g q (digitSymbol x)) (p+1) (q+1) (track x)) := by
  unfold step
  have ht : program.transition (track last) (fun i => (cfg f g p q (track last)).tape i ((cfg f g p q (track last)).head i))=
      some (track x,fun i => if i=0 then (f p,Move.right) else (digitSymbol x,Move.right)) := by
    fin_cases last <;> simp [program,track,cfg,hx,readDigit_symbol]
    all_goals funext i; fin_cases i <;> simp [hx]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk (track x) h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]; intro h; subst z; rfl

theorem copy_run (xs : Word) (last : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ) :
    run program xs.length (cfg (putWord f p (xs.map digitSymbol)) g p q (track last))=
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g q (xs.map digitSymbol))
        (p+xs.length) (q+xs.length) (track (xs.getLastD last))) := by
  induction xs generalizing last f g p q with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := digit_step x last (putWord f p ((x::xs).map digitSymbol)) g p q
      (by rw [List.map_cons,putWord_head])
    rw [List.length_cons,add_comm,run_add,run_one,hs]
    simp only [Option.bind_some,List.map_cons,putWord_cons,List.getLastD_cons]
    have hr := ih x (Function.update f p (digitSymbol x)) (Function.update g q (digitSymbol x)) (p+1) (q+1)
    rw [hr]
    congr 2 <;> push_cast <;> ring

theorem start_step (x : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ)
    (hx : f p=digitSymbol x) :
    step program (cfg f g p q 0)=some (cfg f g (p+1) q (track x)) := by
  unfold step
  have ht : program.transition 0 (fun i => (cfg f g p q 0).tape i ((cfg f g p q 0).head i))=
      some (track x,fun i => (if i=0 then f p else g q,if i=0 then Move.right else Move.stay)) := by
    simp [program,cfg,hx]
    funext i; fin_cases i <;> simp [hx]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk (track x) h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [eq_comm] <;>
      intro h <;> subst z <;> rfl

theorem exit_step (last : Fin 2) (f g : ℤ → Fin 6) (p q : ℤ) (hf : f p=separator) :
    step program (cfg f g p q (track last))=
      some (cfg f (Function.update g q (digitSymbol last)) p (q+1) 3) := by
  unfold step
  have ht : program.transition (track last) (fun i => (cfg f g p q (track last)).tape i ((cfg f g p q (track last)).head i))=
      some (3,fun i => if i=0 then (f p,Move.stay) else (digitSymbol last,Move.right)) := by
    fin_cases last <;> simp [program,track,cfg,hf,readDigit,separator]
    all_goals funext i; fin_cases i <;> simp [hf,separator]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk 3 h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]; intro h; subst z; rfl


theorem separator_step (f g : ℤ → Fin 6) (p q : ℤ) :
    step program (cfg f g p q 3)=
      some (cfg f (Function.update g q separator) (p+1) (q+1) 0) := by
  simp only [step,program,cfg,ite_true,Move.offset]
  congr 1
  apply congrArg₂ (fun h t => Config.mk 0 h t)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]
    intro h; subst z; rfl

def encode (ws : List Word) : List (Fin 6) := (ws.map DelimitedRadixRecord.field).flatten

def volume (ws : List Word) := (encode ws).length

def work (ws : List Word) := volume ws+ws.length

private theorem field_run (x : Fin 2) (xs : Word) (f g : ℤ → Fin 6) (p q : ℤ)
    (hf : f (p+(x::xs).length)=separator) :
    run program ((x::xs).length+2)
      (cfg (putWord f p ((x::xs).map digitSymbol)) g p q 0)=
    some (cfg (putWord f p ((x::xs).map digitSymbol))
      (putWord g q (DelimitedRadixRecord.field (shifted (x::xs))))
      (p+(x::xs).length+1) (q+(x::xs).length+1) 0) := by
  have hs := start_step x (putWord f p ((x::xs).map digitSymbol)) g p q
    (by rw [List.map_cons,putWord_head])
  have hc := copy_run xs x (Function.update f p (digitSymbol x)) g (p+1) q
  rw [←putWord_cons,←List.map_cons] at hc
  have he : putWord f p ((x::xs).map digitSymbol) (p+(x::xs).length)=separator := by
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hf]
  have hxlen : p+1+(xs.length:ℤ)=p+(x::xs).length := by simp; ring
  rw [hxlen] at hc
  have ht := exit_step (xs.getLastD x) (putWord f p ((x::xs).map digitSymbol))
    (putWord g q (xs.map digitSymbol)) (p+(x::xs).length) (q+xs.length) he
  rw [show (x::xs).length+2=1+(xs.length+1+1) by simp; omega,run_add,run_one,hs]
  simp only [Option.bind_some]
  rw [run_add,run_add,hc]
  simp only [Option.bind_some,run_one]
  rw [ht]
  simp only [Option.bind_some]
  rw [separator_step]
  have hg : Function.update (putWord g q (xs.map digitSymbol)) (q+xs.length)
      (digitSymbol (xs.getLastD x)) =
      putWord g q ((shifted (x::xs)).map digitSymbol) := by
    change putWord (putWord g q (xs.map digitSymbol)) (q+xs.length)
      [digitSymbol (xs.getLastD x)] = _
    rw [←List.length_map (f:=digitSymbol) (as:=xs),putWord_append_forward]
    simp only [shifted,List.tail_cons,List.map_append,List.map_singleton,List.getLastD_cons]
  rw [hg]
  have hw : (shifted (x::xs)).length=(x::xs).length :=
    RadixSignedShiftRight.shifted_length _ (by simp)
  have hd : Function.update (putWord g q ((shifted (x::xs)).map digitSymbol))
      (q+xs.length+1) separator = putWord g q (DelimitedRadixRecord.field (shifted (x::xs))) := by
    change putWord (putWord g q ((shifted (x::xs)).map digitSymbol))
      (q+xs.length+1) [separator] = _
    rw [show q+(xs.length:ℤ)+1=q+((shifted (x::xs)).map digitSymbol).length by simp [hw]; ring]
    rw [putWord_append_forward]
    rfl
  rw [hd]
  congr 2; simp; ring

@[simp] theorem encode_cons (w : Word) (ws : List Word) :
    encode (w::ws)=DelimitedRadixRecord.field w++encode ws := by simp [encode]

theorem volume_shifted (ws : List Word) (hn : ∀ w∈ws,w≠[]) :
    volume (ws.map shifted)=volume ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hw := RadixSignedShiftRight.shifted_length w (hn w (by simp))
    have ht := ih (by intro w h; exact hn w (by simp [h]))
    simpa only [volume,List.map_cons,encode_cons,List.length_append,
      DelimitedRadixRecord.field_length,hw] using congrArg (fun n => w.length+1+n) ht

/-- The same finite control handles all literal coefficient fields; separators
physically reset its sign tracker, and no callback supplies a record result. -/
theorem stream_run (ws : List Word) (hn : ∀ w∈ws,w≠[])
    (f g : ℤ → Fin 6) (p q : ℤ) :
    run program (work ws) (cfg (putWord f p (encode ws)) g p q 0)=
      some (cfg (putWord f p (encode ws)) (putWord g q (encode (ws.map shifted)))
        (p+volume ws) (q+volume ws) 0) := by
  induction ws generalizing f g p q with
  | nil => simp [work,volume,encode,putWord,run]
  | cons w ws ih =>
    have hw := hn w (by simp)
    have ht : ∀ w∈ws,w≠[] := by intro w h; exact hn w (by simp [h])
    cases w with
    | nil => contradiction
    | cons x xs =>
      let base := putWord f (p+(x::xs).length) (separator::encode ws)
      have hb : base (p+(x::xs).length)=separator := putWord_head _ _ _ _
      have hs : putWord base p ((x::xs).map digitSymbol)=
          putWord f p (encode ((x::xs)::ws)) := by
        change putWord (putWord f (p+(x::xs).length) (separator::encode ws)) p ((x::xs).map digitSymbol) = _
        rw [show p+(x::xs).length=p+((x::xs).map digitSymbol).length by simp,
          ←putWord_append]
        simp [encode_cons,DelimitedRadixRecord.field,List.append_assoc]
      have hfirst := field_run x xs base g p q hb
      rw [hs] at hfirst
      have hnext := ih ht (putWord f p (DelimitedRadixRecord.field (x::xs)))
        (putWord g q (DelimitedRadixRecord.field (shifted (x::xs))))
        (p+(x::xs).length+1) (q+(x::xs).length+1)
      have hsrc : putWord (putWord f p (DelimitedRadixRecord.field (x::xs)))
          (p+(x::xs).length+1) (encode ws)=putWord f p (encode ((x::xs)::ws)) := by
        rw [show p+(x::xs).length+1=p+(DelimitedRadixRecord.field (x::xs)).length by
          simp [DelimitedRadixRecord.field_length]; ring,putWord_append_forward,encode_cons]
      rw [hsrc] at hnext
      rw [show work ((x::xs)::ws)=(x::xs).length+2+work ws by
        simp [work,volume,encode_cons,DelimitedRadixRecord.field_length]; omega,
        run_add,hfirst]
      simp only [Option.bind_some]
      rw [hnext]
      have hout : putWord (putWord g q (DelimitedRadixRecord.field (shifted (x::xs))))
          (q+(x::xs).length+1) (encode (ws.map shifted))=
          putWord g q (encode (((x::xs)::ws).map shifted)) := by
        rw [show q+(x::xs).length+1=q+(DelimitedRadixRecord.field (shifted (x::xs))).length by
          rw [DelimitedRadixRecord.field_length,RadixSignedShiftRight.shifted_length _ (by simp)]; push_cast; ring,
          putWord_append_forward]
        rfl
      rw [hout]
      congr 2 <;> simp [volume,encode_cons,DelimitedRadixRecord.field_length] <;> ring

/-- Exact scan contract, including genuine halt on the original stream end. -/
theorem runs (ws : List Word) (hn : ∀ w∈ws,w≠[])
    (f g : ℤ → Fin 6) (p q : ℤ) (hf : f (p+volume ws)=blank) :
    HoareTime program
      (fun v => v=tapes (putWord f p (encode ws)) g p q)
      (fun v => v=tapes (putWord f p (encode ws)) (putWord g q (encode (ws.map shifted)))
        (p+volume ws) (q+volume ws)) (work ws) := by
  rintro v rfl
  refine ⟨work ws,_,le_rfl,stream_run ws hn f g p q,?_,rfl⟩
  simp only [step,program,cfg,show (0:Fin 4)≠3 by decide,ite_false]
  have he : putWord f p (encode ws) (p+volume ws)=blank := by
    rw [putWord_outside f p (p+volume ws) (encode ws) (Or.inr (le_refl _))]
    exact hf
  simp [he,readDigit_blank]

theorem work_linear (ws : List Word) : work ws≤2*volume ws := by
  have hl : ws.length≤volume ws := by
    induction ws with
    | nil => simp [volume,encode]
    | cons w ws ih => simp only [volume,encode_cons,List.length_append,
        DelimitedRadixRecord.field_length,List.length_cons] at *; omega
  unfold work
  omega

end IntegerMultBounds.Machine.NativeSignedReturnStream
