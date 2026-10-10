import IntegerMultBounds.Machine.NativeSignedGapPromoteWord
import IntegerMultBounds.Machine.NativeSignedGapClock
import IntegerMultBounds.Machine.WordMoves

/-! One fixed native promotion scanner uses the runtime unary gap clock once
in each direction per field. It emits low zeros, copies the source once, trims
the excess high digits, and restores the clock. No repeated one-bit shift is
used. Only the actual destination suffix is required to be blank. -/
namespace IntegerMultBounds.Machine.NativeSignedGapPromoteScan
open RadixDigits
open RadixSignedShiftRight (Word)
open NativeSignedGapScan (clock clock_digit clock_end clock_origin)
open NativeSignedGapPromoteWord (result result_length)

/-- Source, generated output and reusable runtime gap clock. -/
def program : Program 3 4 2 where
  tapes_pos := by decide
  start := 0
  transition := fun state sy =>
    if state=0 then
      if sy 0=blank then none
      else if sy 2=blank then some (1,fun i => (sy i,.stay))
      else some (0,fun i => (if i=1 then digitSymbol (0:Fin 2) else sy i,
        if i=0 then .stay else .right))
    else if state=1 then
      match readDigit (sy 0) with
      | some x => some (1,fun i => (if i=1 then digitSymbol x else sy i,
          if i=2 then .stay else .right))
      | none => some (2,fun i => (sy i,if i=0 then .stay else .left))
    else if state=2 then
      if sy 2=separator then some (3,fun i => (sy i,.right))
      else some (2,fun i => (if i=1 then blank else sy i,if i=0 then .stay else .left))
    else some (0,fun i => (if i=1 then separator else sy i,if i=1 then .right else .stay))

def cfg (f g h : ℤ → Fin 6) (p q r : ℤ) (state : Fin 4) : Config 3 4 2 :=
  ⟨state,![p,q,r],![f,g,h]⟩
def tapes (f g h : ℤ → Fin 6) (p q r : ℤ) := (cfg f g h p q r 0).tapes

private theorem step_at (st st' : Fin 4) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (x : Fin 6) (mv : Fin 3 → Move)
    (ht : program.transition st (fun i => (![f,g,h] i) (![p,q,r] i))=
      some (st',fun i => (if i=1 then x else (![f,g,h] i) (![p,q,r] i),mv i))) :
    step program (cfg f g h p q r st)=
      some (cfg f (Function.update g q x) h (p+(mv 0).offset) (q+(mv 1).offset) (r+(mv 2).offset) st') := by
  simp only [step,cfg]
  rw [ht]
  dsimp only
  congr 1
  apply congrArg₂ (fun hs ts => Config.mk st' hs ts)
  · funext i; fin_cases i <;> rfl
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]
    all_goals intro he; subst z; rfl

private theorem zero_step (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p≠blank) (hc : h r≠blank) :
    step program (cfg f g h p q r 0)=
      some (cfg f (Function.update g q (digitSymbol (0:Fin 2))) h p (q+1) (r+1) 0) := by
  simpa [Move.offset,add_zero] using
    step_at 0 0 f g h p q r (digitSymbol (0:Fin 2)) (fun i => if i=0 then .stay else .right)
      (by simp [program,hf,hc])

private theorem handoff_step (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p≠blank) (hc : h r=blank) :
    step program (cfg f g h p q r 0)=some (cfg f g h p q r 1) := by
  have hu : Function.update g q (g q)=g := Function.update_eq_self_iff.mpr rfl
  simpa only [Move.offset,add_zero,hu] using step_at 0 1 f g h p q r (g q) (fun _ => .stay)
    (by simp [program,hf,hc]; funext i; fin_cases i <;> simp)

private theorem copy_step (x : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p=digitSymbol x) :
    step program (cfg f g h p q r 1)=
      some (cfg f (Function.update g q (digitSymbol x)) h (p+1) (q+1) r 1) := by
  simpa [Move.offset,add_zero] using step_at 1 1 f g h p q r (digitSymbol x)
    (fun i => if i=2 then .stay else .right) (by simp [program,hf])

private theorem begin_trim_step (f g h : ℤ → Fin 6) (p q r : ℤ) (hf : f p=separator) :
    step program (cfg f g h p q r 1)=some (cfg f g h p (q-1) (r-1) 2) := by
  have hu : Function.update g q (g q)=g := Function.update_eq_self_iff.mpr rfl
  simpa [Move.offset,add_zero,hu,sub_eq_add_neg] using
    step_at 1 2 f g h p q r (g q) (fun i => if i=0 then .stay else .left)
      (by simp [program,hf,readDigit,separator]; funext i; fin_cases i <;> simp)

private theorem trim_step (f g h : ℤ → Fin 6) (p q r : ℤ) (hc : h r≠separator) :
    step program (cfg f g h p q r 2)=some (cfg f (Function.update g q blank) h p (q-1) (r-1) 2) := by
  simpa [Move.offset,add_zero,sub_eq_add_neg] using
    step_at 2 2 f g h p q r blank (fun i => if i=0 then .stay else .left) (by simp [program,hc])

private theorem finish_trim_step (f g h : ℤ → Fin 6) (p q r : ℤ) (hc : h r=separator) :
    step program (cfg f g h p q r 2)=some (cfg f g h (p+1) (q+1) (r+1) 3) := by
  have hu : Function.update g q (g q)=g := Function.update_eq_self_iff.mpr rfl
  simpa only [Move.offset,hu] using step_at 2 3 f g h p q r (g q) (fun _ => .right)
    (by simp [program,hc]; funext i; fin_cases i <;> simp)

private theorem separator_step (f g h : ℤ → Fin 6) (p q r : ℤ) :
    step program (cfg f g h p q r 3)=some (cfg f (Function.update g q separator) h p (q+1) r 0) := by
  simpa [Move.offset,add_zero] using step_at 3 0 f g h p q r separator
    (fun i => if i=1 then .right else .stay) (by simp [program])

private theorem zero_run (d : ℕ) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p≠blank) (hc : ∀ i:ℕ,i<d → h (r+i)≠blank) :
    run program d (cfg f g h p q r 0)=
      some (cfg f (putWord g q (List.replicate d (digitSymbol (0:Fin 2)))) h p (q+d) (r+d) 0) := by
  induction d generalizing g q r with
  | zero => simp [run,putWord]
  | succ d ih =>
    rw [show d+1=1+d by omega,run_add,run_one,zero_step f g h p q r hf (by simpa using hc 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (Function.update g q (digitSymbol (0:Fin 2))) (q+1) (r+1)
      (by intro i hi; simpa only [show r+1+(i:ℤ)=r+(i+1:ℕ) by push_cast; ring] using hc (i+1) (by omega))]
    rw [show 1+d=d+1 by omega,List.replicate_succ,putWord_cons]
    congr 2 <;> push_cast <;> ring

private theorem copy_run (xs : Word) (f g h : ℤ → Fin 6) (p q r : ℤ) :
    run program xs.length (cfg (putWord f p (xs.map digitSymbol)) g h p q r 1)=
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g q (xs.map digitSymbol)) h
        (p+xs.length) (q+xs.length) r 1) := by
  induction xs generalizing f g p q with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    rw [List.length_cons,add_comm,run_add,run_one,copy_step x (putWord f p ((x::xs).map digitSymbol)) g h p q r
      (by rw [List.map_cons,putWord_head])]
    simp only [Option.bind_some,List.map_cons,putWord_cons]
    rw [ih (Function.update f p (digitSymbol x)) (Function.update g q (digitSymbol x)) (p+1) (q+1)]
    congr 2 <;> push_cast <;> ring

private theorem trim_run (n : ℕ) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hc : ∀ i:ℕ,i<n → h (r+i)≠separator) :
    run program n (cfg f g h p (q+n-1) (r+n-1) 2)=
      some (cfg f (EraseBack.eraseRange g q n) h p (q-1) (r-1) 2) := by
  induction n generalizing g with
  | zero => simp [run,EraseBack.eraseRange_zero]
  | succ n ih =>
    rw [show q+(n+1:ℕ)-1=q+n by push_cast; ring,
      show r+(n+1:ℕ)-1=r+n by push_cast; ring,show n+1=1+n by omega,run_add,run_one,
      trim_step f g h p (q+n) (r+n) (hc n (by omega))]
    simp only [Option.bind_some]
    rw [show q+(n:ℤ)-1=q+n-1 by ring,show r+(n:ℤ)-1=r+n-1 by ring,
      ih (Function.update g (q+n) blank) (fun i hi => hc i (by omega)),EraseBack.eraseRange_succ]
    simp only [Nat.add_comm]

/-- One field requires a real blank suffix beyond its intended output. Temporary
high digits are erased before the next field is emitted, restoring that suffix. -/
theorem field_run (xs : Word) (d : ℕ) (hd : d≤xs.length)
    (f g : ℤ → Fin 6) (p q : ℤ) (hf : f (p+xs.length)=separator)
    (hg : ∀ i:ℕ,i<d → g (q+xs.length+i)=blank) :
    run program (xs.length+2*d+4)
      (cfg (putWord f p (xs.map digitSymbol)) g (clock d) p q 1 0)=
    some (cfg (putWord f p (xs.map digitSymbol))
      (putWord g q (DelimitedRadixRecord.field (result d xs))) (clock d)
      (p+xs.length+1) (q+xs.length+1) 1 0) := by
  let src := putWord f p (xs.map digitSymbol)
  have hs : src (p+xs.length)=separator := by
    dsimp only [src]
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hf]
  have hn : src p≠blank := by
    cases xs with
    | nil =>
      have hz : src p=separator := by simpa using hs
      rw [hz]; decide
    | cons x xs =>
      dsimp only [src]
      rw [List.map_cons,putWord_head]
      intro he; have hv := congrArg Fin.val he; change x.val+4=0 at hv; omega
  have h0 := zero_run d src g (clock d) p q 1 hn (by
    intro i hi
    rw [clock_digit d i hi]
    decide)
  let gz := putWord g q (List.replicate d (digitSymbol (0:Fin 2)))
  have h1 := handoff_step src gz (clock d) p (q+d) (1+d) hn (clock_end d)
  have h2 := copy_run xs f gz (clock d) p (q+d) (1+d)
  let raw := putWord gz (q+d) (xs.map digitSymbol)
  have h3 := begin_trim_step src raw (clock d) (p+xs.length) (q+d+xs.length) (1+d) hs
  have h4 := trim_run d src raw (clock d) (p+xs.length) (q+xs.length) 1 (by
    intro i hi
    rw [clock_digit d i hi]
    exact DelimitedRadixRecord.digit_ne_separator _)
  have he : EraseBack.eraseRange raw (q+xs.length) d=
      putWord g q ((result d xs).map digitSymbol) := by
    let lo := xs.take (xs.length-d)
    let hi := xs.drop (xs.length-d)
    have hlo : lo.length=xs.length-d := by simp only [lo,List.length_take,min_eq_left (Nat.sub_le _ _)]
    have hhi : hi.length=d := by simp [hi]; omega
    have hxs : lo++hi=xs := List.take_append_drop _ _
    have hp : (List.replicate d (0:Fin 2)++lo).length=xs.length := by simp; omega
    have hr : raw=putWord (putWord g q ((List.replicate d (0:Fin 2)++lo).map digitSymbol))
        (q+xs.length) (hi.map digitSymbol) := by
      dsimp only [raw,gz]
      rw [show q+(d:ℤ)=q+(List.replicate d (digitSymbol (0:Fin 2))).length by simp,putWord_append_forward]
      have hm : List.replicate d (digitSymbol (0:Fin 2)) ++ xs.map digitSymbol =
          ((List.replicate d (0:Fin 2)++lo).map digitSymbol)++hi.map digitSymbol := by
        rw [←hxs,List.map_append,List.map_append,List.map_replicate,List.append_assoc]
      rw [hm,←putWord_append_forward]
      simp only [List.length_map,hp]
    have hblank : ∀ i:ℕ, i<(hi.map digitSymbol).length →
        putWord g q ((List.replicate d (0:Fin 2)++lo).map digitSymbol)
          (q+xs.length+i)=blank := by
      intro i hi'
      rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map,hp]; omega))]
      exact hg i (by simpa only [List.length_map,hhi] using hi')
    rw [hr]
    have her := EraseBack.eraseRange_putWord _ _ _ hblank
    simp only [List.length_map,hhi] at her
    rw [her]
    congr 1
    simp only [result,min_eq_left hd,lo]
  rw [he] at h4
  have h5 := finish_trim_step src (putWord g q ((result d xs).map digitSymbol)) (clock d)
    (p+xs.length) (q+xs.length-1) 0 (clock_origin d)
  have h6 := separator_step src (putWord g q ((result d xs).map digitSymbol)) (clock d)
    (p+xs.length+1) (q+xs.length) 1
  have ho : Function.update (putWord g q ((result d xs).map digitSymbol)) (q+xs.length) separator=
      putWord g q (DelimitedRadixRecord.field (result d xs)) := by
    change putWord (putWord g q ((result d xs).map digitSymbol)) (q+xs.length) [separator]=_
    rw [show q+xs.length=q+((result d xs).map digitSymbol).length by rw [List.length_map,result_length],putWord_append_forward]
    rfl
  rw [show xs.length+2*d+4=d+1+xs.length+1+d+1+1 by omega,
    run_add,run_add,run_add,run_add,run_add,run_add,h0]
  simp only [Option.bind_some,run_one]
  rw [h1]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.bind_some]
  rw [h3]
  simp only [Option.bind_some]
  rw [show q+(d:ℤ)+xs.length-1=q+xs.length+d-1 by ring,
    show (1:ℤ)+d-1=1+d-1 by ring,h4]
  simp only [Option.bind_some]
  rw [show (1:ℤ)-1=0 by ring,h5]
  simp only [Option.bind_some]
  rw [show q+(xs.length:ℤ)-1+1=q+xs.length by ring,show (0:ℤ)+1=1 by ring,h6,ho]

def work (d : ℕ) (ws : List Word) := NativeSignedReturnStream.volume ws+(2*d+3)*ws.length

theorem stream_run (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length)
    (f g : ℤ → Fin 6) (p q : ℤ) (hg : ∀ z, q≤z → g z=blank) :
    run program (work d ws)
      (cfg (putWord f p (NativeSignedReturnStream.encode ws)) g (clock d) p q 1 0)=
    some (cfg (putWord f p (NativeSignedReturnStream.encode ws))
      (putWord g q (NativeSignedReturnStream.encode (ws.map (result d)))) (clock d)
      (p+NativeSignedReturnStream.volume ws) (q+NativeSignedReturnStream.volume ws) 1 0) := by
  induction ws generalizing f g p q with
  | nil => simp [work,NativeSignedReturnStream.volume,NativeSignedReturnStream.encode,run,putWord]
  | cons w ws ih =>
    have hw := hd w (by simp)
    have ht : ∀ w∈ws,d≤w.length := by intro w h; exact hd w (by simp [h])
    let base := putWord f (p+w.length) (separator::NativeSignedReturnStream.encode ws)
    have hb : base (p+w.length)=separator := putWord_head _ _ _ _
    have hs : putWord base p (w.map digitSymbol)=putWord f p (NativeSignedReturnStream.encode (w::ws)) := by
      change putWord (putWord f (p+w.length) (separator::NativeSignedReturnStream.encode ws)) p (w.map digitSymbol)=_
      rw [show p+w.length=p+(w.map digitSymbol).length by simp,←putWord_append]
      simp [NativeSignedReturnStream.encode_cons,DelimitedRadixRecord.field,List.append_assoc]
    have hfirst := field_run w d hw base g p q hb (by intro i hi; apply hg; omega)
    rw [hs] at hfirst
    have hnext := ih ht (putWord f p (DelimitedRadixRecord.field w))
      (putWord g q (DelimitedRadixRecord.field (result d w))) (p+w.length+1) (q+w.length+1) (by
        intro z hz
        rw [putWord_outside _ _ _ _ (Or.inr (by
          simp only [DelimitedRadixRecord.field_length,result_length]; omega))]
        apply hg; omega)
    have hsrc : putWord (putWord f p (DelimitedRadixRecord.field w))
        (p+w.length+1) (NativeSignedReturnStream.encode ws)=putWord f p (NativeSignedReturnStream.encode (w::ws)) := by
      rw [show p+w.length+1=p+(DelimitedRadixRecord.field w).length by simp [DelimitedRadixRecord.field_length]; ring,
        putWord_append_forward,NativeSignedReturnStream.encode_cons]
    rw [hsrc] at hnext
    rw [show work d (w::ws)=w.length+2*d+4+work d ws by
      simp [work,NativeSignedReturnStream.volume,NativeSignedReturnStream.encode_cons,DelimitedRadixRecord.field_length]; ring,
      run_add,hfirst]
    simp only [Option.bind_some]
    rw [hnext]
    have hout : putWord (putWord g q (DelimitedRadixRecord.field (result d w)))
        (q+w.length+1) (NativeSignedReturnStream.encode (ws.map (result d)))=
        putWord g q (NativeSignedReturnStream.encode ((w::ws).map (result d))) := by
      rw [show q+w.length+1=q+(DelimitedRadixRecord.field (result d w)).length by
        rw [DelimitedRadixRecord.field_length,result_length]; push_cast; ring,putWord_append_forward]
      rfl
    rw [hout]
    congr 2 <;> simp [NativeSignedReturnStream.volume,NativeSignedReturnStream.encode_cons,
      DelimitedRadixRecord.field_length] <;> ring

theorem volume_result (ws : List Word) (d : ℕ) :
    NativeSignedReturnStream.volume (ws.map (result d))=NativeSignedReturnStream.volume ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa only [NativeSignedReturnStream.volume,List.map_cons,
      NativeSignedReturnStream.encode_cons,List.length_append,DelimitedRadixRecord.field_length,result_length] using (congrArg (fun n => w.length+1+n) ih)

theorem runs (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length)
    (f g : ℤ → Fin 6) (p q : ℤ) (hg : ∀ z, q≤z → g z=blank)
    (hf : f (p+NativeSignedReturnStream.volume ws)=blank) :
    HoareTime program
      (fun v => v=tapes (putWord f p (NativeSignedReturnStream.encode ws)) g (clock d) p q 1)
      (fun v => v=tapes (putWord f p (NativeSignedReturnStream.encode ws))
        (putWord g q (NativeSignedReturnStream.encode (ws.map (result d)))) (clock d)
        (p+NativeSignedReturnStream.volume ws) (q+NativeSignedReturnStream.volume ws) 1) (work d ws) := by
  rintro v rfl
  refine ⟨work d ws,_,le_rfl,stream_run ws d hd f g p q hg,?_,rfl⟩
  have he : putWord f p (NativeSignedReturnStream.encode ws)
      (p+NativeSignedReturnStream.volume ws)=blank := by
    rw [putWord_outside f p (p+NativeSignedReturnStream.volume ws) _ (Or.inr (le_refl _))]
    exact hf
  simp [step,program,cfg,he]

theorem work_linear (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length) :
    work d ws≤4*NativeSignedReturnStream.volume ws := by
  induction ws with
  | nil => simp [work,NativeSignedReturnStream.volume,NativeSignedReturnStream.encode]
  | cons w ws ih =>
    have hw := hd w (by simp)
    have ht := ih (by intro w h; exact hd w (by simp [h]))
    simp only [work,NativeSignedReturnStream.volume,NativeSignedReturnStream.encode_cons,
      List.length_append,DelimitedRadixRecord.field_length,List.length_cons] at *
    nlinarith


end IntegerMultBounds.Machine.NativeSignedGapPromoteScan
