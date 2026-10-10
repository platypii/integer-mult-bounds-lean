import IntegerMultBounds.Machine.NativeSignedReturnPrecision
import IntegerMultBounds.Machine.WordSegments

/-! A single scan per native signed field with a reusable runtime unary gap
clock. The clock traverses only the skipped prefix and returns to its origin;
remaining digits and sign extension are emitted directly. -/
namespace IntegerMultBounds.Machine.NativeSignedGapScan
open RadixDigits
open RadixSignedShiftRight (Word)

def skipState (last : Fin 2) : Fin 6 := ⟨last.val,by omega⟩
def copyState (last : Fin 2) : Fin 6 := ⟨last.val+2,by omega⟩
def fillState (last : Fin 2) : Fin 6 := ⟨last.val+4,by omega⟩
def sign (state : Fin 6) : Fin 2 := if state.val%2=0 then 0 else 1

def program : Program 3 6 2 where
  tapes_pos := by decide
  start := 0
  transition := fun state sy =>
    if state.val<2 then
      if sy 0=blank then none
      else if sy 2=blank then some (copyState (sign state),fun i => (sy i,.stay))
      else match readDigit (sy 0) with
        | some x => some (skipState x,fun i => (sy i,if i=1 then .stay else .right))
        | none => some (fillState (sign state),fun i => (sy i,if i=2 then .left else .stay))
    else if state.val<4 then
      match readDigit (sy 0) with
      | some x => some (copyState x,fun i => (if i=1 then digitSymbol x else sy i,
          if i=2 then .stay else .right))
      | none => some (fillState (sign state),fun i => (sy i,if i=2 then .left else .stay))
    else if sy 2=separator then some (0,fun i =>
      (if i=1 then separator else sy i,.right))
    else some (state,fun i => (if i=1 then digitSymbol (sign state) else sy i,
      if i=0 then .stay else if i=1 then .right else .left))

def cfg (f g h : ℤ → Fin 6) (p q r : ℤ) (state : Fin 6) : Config 3 6 2 :=
  ⟨state,![p,q,r],![f,g,h]⟩
def tapes (f g h : ℤ → Fin 6) (p q r : ℤ) := (cfg f g h p q r 0).tapes

def clock (d : ℕ) : ℤ → Fin 6 :=
  putWord (fun z => if z=0 then separator else blank) 1 (List.replicate d (digitSymbol (0:Fin 2)))

theorem clock_digit (d i : ℕ) (hi : i<d) : clock d (1+i)=digitSymbol (0:Fin 2) := by
  rw [clock,WordSegments.get _ _ _ i (by simpa using hi)]
  simp

theorem clock_end (d : ℕ) : clock d (1+d)=blank := by
  rw [clock,putWord_outside _ _ _ _ (Or.inr (by simp))]
  simp [show (1:ℤ)+d≠0 by omega]

theorem clock_origin (d : ℕ) : clock d 0=separator := by
  rw [clock,putWord_outside _ _ _ _ (Or.inl (by omega))]
  simp

private theorem retained_update (f : ℤ → Fin 6) (p : ℤ) : Function.update f p (f p)=f := by
  funext z; by_cases hz:z=p <;> simp [hz]

private theorem skip_step (x last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p=digitSymbol x) (hc : h r≠blank) :
    step program (cfg f g h p q r (skipState last))=
      some (cfg f g h (p+1) q (r+1) (skipState x)) := by
  have hd : digitSymbol x≠blank := by intro he; have hv:=congrArg Fin.val he; change x.val+4=0 at hv; omega
  unfold step
  have ht : program.transition (skipState last) (fun i => (cfg f g h p q r (skipState last)).tape i
      ((cfg f g h p q r (skipState last)).head i))=
      some (skipState x,fun i => ((![f,g,h] i) (![p,q,r] i),if i=1 then Move.stay else Move.right)) := by
    fin_cases last <;> simp [program,skipState,cfg,hf,hc,hd]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun hs ts => Config.mk (skipState x) hs ts)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [eq_comm]
    all_goals intro he; subst z; rfl

private theorem copy_step (x last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p=digitSymbol x) :
    step program (cfg f g h p q r (copyState last))=
      some (cfg f (Function.update g q (digitSymbol x)) h (p+1) (q+1) r (copyState x)) := by
  unfold step
  have ht : program.transition (copyState last) (fun i => (cfg f g h p q r (copyState last)).tape i
      ((cfg f g h p q r (copyState last)).head i))=
      some (copyState x,fun i => (if i=1 then digitSymbol x else (![f,g,h] i) (![p,q,r] i),
        if i=2 then Move.stay else Move.right)) := by
    fin_cases last <;> simp [program,copyState,cfg,hf]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun hs ts => Config.mk (copyState x) hs ts)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]
    all_goals intro he; subst z; rfl

private theorem retained_step (st st' : Fin 6) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (mv : Fin 3 → Move)
    (ht : program.transition st (fun i => (![f,g,h] i) (![p,q,r] i))=
      some (st',fun i => ((![f,g,h] i) (![p,q,r] i),mv i))) :
    step program (cfg f g h p q r st)=
      some (cfg f g h (p+(mv 0).offset) (q+(mv 1).offset) (r+(mv 2).offset) st') := by
  simp only [step,cfg]
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun hs ts => Config.mk st' hs ts)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [eq_comm]
    all_goals intro he; subst z; rfl

private theorem handoff_step (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p≠blank) (hc : h r=blank) :
    step program (cfg f g h p q r (skipState last))=
      some (cfg f g h p q r (copyState last)) := by
  simpa [Move.offset,sub_eq_add_neg] using retained_step (skipState last) (copyState last) f g h p q r (fun _ => .stay)
    (by fin_cases last <;> simp [program,skipState,copyState,sign,hf,hc])

private theorem begin_fill_step (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hf : f p=separator) :
    step program (cfg f g h p q r (copyState last))=
      some (cfg f g h p q (r-1) (fillState last)) := by
  simpa [Move.offset,sub_eq_add_neg] using retained_step (copyState last) (fillState last) f g h p q r
    (fun i => if i=2 then .left else .stay)
    (by fin_cases last <;> simp [program,copyState,fillState,sign,hf,readDigit,separator])

private theorem fill_step (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hc : h r≠separator) :
    step program (cfg f g h p q r (fillState last))=
      some (cfg f (Function.update g q (digitSymbol last)) h p (q+1) (r-1) (fillState last)) := by
  unfold step
  have ht : program.transition (fillState last) (fun i => (cfg f g h p q r (fillState last)).tape i
      ((cfg f g h p q r (fillState last)).head i))=
      some (fillState last,fun i => (if i=1 then digitSymbol last else (![f,g,h] i) (![p,q,r] i),
        if i=0 then Move.stay else if i=1 then Move.right else Move.left)) := by
    fin_cases last <;> simp [program,fillState,sign,cfg,hc]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun hs ts => Config.mk (fillState last) hs ts)
  · funext i; fin_cases i <;> simp; ring
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]
    all_goals intro he; subst z; rfl

private theorem finish_step (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hc : h r=separator) :
    step program (cfg f g h p q r (fillState last))=
      some (cfg f (Function.update g q separator) h (p+1) (q+1) (r+1) 0) := by
  unfold step
  have ht : program.transition (fillState last) (fun i => (cfg f g h p q r (fillState last)).tape i
      ((cfg f g h p q r (fillState last)).head i))=
      some (0,fun i => (if i=1 then separator else (![f,g,h] i) (![p,q,r] i),Move.right)) := by
    fin_cases last <;> simp [program,fillState,cfg,hc]
  simp only [cfg] at ht ⊢
  rw [ht]
  simp only [Move.offset]
  congr 1
  apply congrArg₂ (fun hs ts => Config.mk 0 hs ts)
  · funext i; fin_cases i <;> simp
  · funext i z; fin_cases i <;> simp [Function.update_apply,eq_comm]
    all_goals intro he; subst z; rfl

private theorem skip_run (xs : Word) (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hc : ∀ i:ℕ,i<xs.length → h (r+i)≠blank) :
    run program xs.length (cfg (putWord f p (xs.map digitSymbol)) g h p q r (skipState last))=
      some (cfg (putWord f p (xs.map digitSymbol)) g h (p+xs.length) q (r+xs.length)
        (skipState (xs.getLastD last))) := by
  induction xs generalizing f p r last with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := skip_step x last (putWord f p ((x::xs).map digitSymbol)) g h p q r
      (by rw [List.map_cons,putWord_head]) (by simpa using hc 0 (by simp))
    rw [List.length_cons,add_comm,run_add,run_one,hs]
    simp only [Option.bind_some,List.map_cons,putWord_cons,List.getLastD_cons]
    rw [ih x (Function.update f p (digitSymbol x)) (p+1) (r+1)
      (by intro i hi; simpa only [show r+1+(i:ℤ)=r+(i+1:ℕ) by push_cast; ring] using hc (i+1) (by simp; omega))]
    congr 2 <;> push_cast <;> ring

private theorem copy_run (xs : Word) (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ) :
    run program xs.length (cfg (putWord f p (xs.map digitSymbol)) g h p q r (copyState last))=
      some (cfg (putWord f p (xs.map digitSymbol)) (putWord g q (xs.map digitSymbol)) h
        (p+xs.length) (q+xs.length) r (copyState (xs.getLastD last))) := by
  induction xs generalizing last f g p q with
  | nil => simp [run,putWord]
  | cons x xs ih =>
    have hs := copy_step x last (putWord f p ((x::xs).map digitSymbol)) g h p q r
      (by rw [List.map_cons,putWord_head])
    rw [List.length_cons,add_comm,run_add,run_one,hs]
    simp only [Option.bind_some,List.map_cons,putWord_cons,List.getLastD_cons]
    rw [ih x (Function.update f p (digitSymbol x)) (Function.update g q (digitSymbol x)) (p+1) (q+1)]
    congr 2 <;> push_cast <;> ring

private theorem fill_run (n : ℕ) (last : Fin 2) (f g h : ℤ → Fin 6) (p q r : ℤ)
    (hc : ∀ i:ℕ,i<n → h (r-i)≠separator) :
    run program n (cfg f g h p q r (fillState last))=
      some (cfg f (putWord g q (List.replicate n (digitSymbol last))) h p (q+n) (r-n) (fillState last)) := by
  induction n generalizing g q r with
  | zero => simp [run,putWord]
  | succ n ih =>
    rw [show n+1=1+n by omega,run_add,run_one,fill_step last f g h p q r (by simpa using hc 0 (by omega))]
    simp only [Option.bind_some]
    rw [ih (Function.update g q (digitSymbol last)) (q+1) (r-1)
      (by intro i hi; simpa only [show r-1-(i:ℤ)=r-(i+1:ℕ) by push_cast; ring] using hc (i+1) (by omega))]
    rw [show 1+n=n+1 by omega,List.replicate_succ,putWord_cons]
    congr 2 <;> push_cast <;> ring

private theorem last_append (lo hi : Word) (a : Fin 2) :
    (lo++hi).getLastD a=hi.getLastD (lo.getLastD a) := by
  induction lo generalizing a with
  | nil => simp only [List.nil_append,List.getLastD_nil]
  | cons x lo ih => rw [List.cons_append,List.getLastD_cons,ih,List.getLastD_cons]

def result (d : ℕ) (xs : Word) := xs.drop d++List.replicate (min d xs.length) (xs.getLastD 0)

/-- A gap clock is scanned only once in each direction per field. This literal
run copies the suffix and appends exactly the skipped number of sign digits. -/
theorem field_run (lo hi : Word) (f g : ℤ → Fin 6) (p q : ℤ)
    (hf : f (p+(lo++hi).length)=separator) :
    run program ((lo++hi).length+lo.length+3)
      (cfg (putWord f p ((lo++hi).map digitSymbol)) g (clock lo.length) p q 1 0)=
    some (cfg (putWord f p ((lo++hi).map digitSymbol))
      (putWord g q (DelimitedRadixRecord.field (hi++List.replicate lo.length ((lo++hi).getLastD 0))))
      (clock lo.length) (p+(lo++hi).length+1) (q+(lo++hi).length+1) 1 0) := by
  let src := putWord f p ((lo++hi).map digitSymbol)
  have hskip := skip_run lo 0 (putWord f (p+lo.length) (hi.map digitSymbol)) g (clock lo.length) p q 1
    (by intro i hi; rw [clock_digit _ i hi]; intro he; have hh:=congrArg Fin.val he; norm_num [digitSymbol,blank] at hh)
  have hs : putWord (putWord f (p+lo.length) (hi.map digitSymbol)) p (lo.map digitSymbol)=src := by
    dsimp only [src]
    rw [←List.length_map (f:=digitSymbol) (as:=lo),←putWord_append,←List.map_append]
  rw [hs,show skipState (0:Fin 2)=0 by rfl] at hskip
  have hcopy := copy_run hi (lo.getLastD 0) (putWord f p (lo.map digitSymbol)) g
    (clock lo.length) (p+lo.length) q (1+lo.length)
  have ht : putWord (putWord f p (lo.map digitSymbol)) (p+lo.length) (hi.map digitSymbol)=src := by
    dsimp only [src]
    rw [←List.length_map (f:=digitSymbol) (as:=lo),putWord_append_forward,←List.map_append]
  rw [ht,←last_append] at hcopy
  have hp : p+(lo.length:ℤ)+hi.length=p+(lo++hi).length := by simp; ring
  rw [hp] at hcopy
  have hsep : src (p+(lo++hi).length)=separator := by
    dsimp only [src]
    rw [putWord_outside _ _ _ _ (Or.inr (by simp)),hf]
  have hnon : src (p+lo.length)≠blank := by
    cases hi with
    | nil =>
      have he : src (p+lo.length)=separator := by simpa only [List.append_nil] using hsep
      rw [he]
      decide
    | cons x hi =>
      rw [←ht,List.map_cons,putWord_head]
      intro he; have hh:=congrArg Fin.val he; change x.val+4=0 at hh; omega
  have hh := handoff_step (lo.getLastD 0) src g (clock lo.length) (p+lo.length) q (1+lo.length)
    hnon (clock_end _)
  have hb := begin_fill_step ((lo++hi).getLastD 0) src (putWord g q (hi.map digitSymbol))
    (clock lo.length) (p+(lo++hi).length) (q+hi.length) (1+lo.length) hsep
  have hfill := fill_run lo.length ((lo++hi).getLastD 0) src (putWord g q (hi.map digitSymbol))
    (clock lo.length) (p+(lo++hi).length) (q+hi.length) lo.length (by
      intro i hi
      rw [show (lo.length:ℤ)-i=1+((lo.length-1-i:ℕ):ℤ) by omega,clock_digit _ _ (by omega)]
      exact DelimitedRadixRecord.digit_ne_separator _)
  have hend := finish_step ((lo++hi).getLastD 0) src
    (putWord (putWord g q (hi.map digitSymbol)) (q+hi.length)
      (List.replicate lo.length (digitSymbol ((lo++hi).getLastD 0))))
    (clock lo.length) (p+(lo++hi).length) (q+hi.length+lo.length) 0 (clock_origin _)
  rw [show (lo++hi).length+lo.length+3=lo.length+1+hi.length+1+lo.length+1 by simp; omega,
    run_add,run_add,run_add,run_add,run_add,hskip]
  simp only [Option.bind_some,run_one]
  rw [hh]
  simp only [Option.bind_some]
  rw [hcopy]
  simp only [Option.bind_some]
  rw [hb]
  simp only [Option.bind_some]
  rw [show (1:ℤ)+lo.length-1=lo.length by ring,hfill]
  simp only [Option.bind_some]
  rw [sub_self,hend]
  have hg : putWord (putWord g q (hi.map digitSymbol)) (q+hi.length)
      (List.replicate lo.length (digitSymbol ((lo++hi).getLastD 0)))=
      putWord g q ((hi++List.replicate lo.length ((lo++hi).getLastD 0)).map digitSymbol) := by
    rw [←List.length_map (f:=digitSymbol) (as:=hi),putWord_append_forward,List.map_append,List.map_replicate]
  rw [hg]
  have hw : (hi++List.replicate lo.length ((lo++hi).getLastD 0)).length=(lo++hi).length := by simp; omega
  have hd : Function.update (putWord g q ((hi++List.replicate lo.length ((lo++hi).getLastD 0)).map digitSymbol))
      (q+hi.length+lo.length) separator=
      putWord g q (DelimitedRadixRecord.field (hi++List.replicate lo.length ((lo++hi).getLastD 0))) := by
    change putWord (putWord g q ((hi++List.replicate lo.length ((lo++hi).getLastD 0)).map digitSymbol))
      (q+hi.length+lo.length) [separator]=_
    rw [show q+(hi.length:ℤ)+lo.length=q+((hi++List.replicate lo.length ((lo++hi).getLastD 0)).map digitSymbol).length by simp; ring,
      putWord_append_forward]
    rfl
  rw [hd]
  congr 2; simp; ring

theorem result_length (d : ℕ) (xs : Word) : (result d xs).length=xs.length := by
  simp only [result,List.length_append,List.length_drop,List.length_replicate]
  omega

private theorem result_last (d : ℕ) (xs : Word) (_hn : xs≠[]) (hd : d≤xs.length) :
    (result d xs).getLastD 0=xs.getLastD 0 := by
  cases d with
  | zero => simp [result]
  | succ d =>
    simp only [result,min_eq_left hd]
    rw [show d+1=d+1 by rfl,List.replicate_add,List.replicate_one,←List.append_assoc,List.getLastD_concat]

private theorem result_succ (d : ℕ) (xs : Word) (hn : xs≠[]) (hd : d+1≤xs.length) :
    result (d+1) xs=RadixSignedShiftRight.shifted (result d xs) := by
  have hdrop : xs.drop d≠[] := by intro he; have hh:=List.drop_eq_nil_iff.mp he; omega
  rw [RadixSignedShiftRight.shifted,result_last d xs hn (by omega)]
  simp only [result,min_eq_left hd,min_eq_left (show d≤xs.length by omega)]
  rw [List.tail_append_of_ne_nil hdrop,List.tail_drop,List.replicate_add,List.replicate_one,List.append_assoc]

theorem result_iterate (d : ℕ) (xs : Word) (hn : xs≠[]) (hd : d≤xs.length) :
    result d xs=(RadixSignedShiftRight.shifted^[d]) xs := by
  induction d with
  | zero => simp [result]
  | succ d ih => rw [result_succ d xs hn hd,ih (by omega),Function.iterate_succ_apply']

theorem field_run_gap (xs : Word) (d : ℕ) (hd : d≤xs.length)
    (f g : ℤ → Fin 6) (p q : ℤ) (hf : f (p+xs.length)=separator) :
    run program (xs.length+d+3) (cfg (putWord f p (xs.map digitSymbol)) g (clock d) p q 1 0)=
    some (cfg (putWord f p (xs.map digitSymbol))
      (putWord g q (DelimitedRadixRecord.field (result d xs))) (clock d)
      (p+xs.length+1) (q+xs.length+1) 1 0) := by
  have hh := field_run (xs.take d) (xs.drop d) f g p q (by simpa using hf)
  simpa only [List.take_append_drop,List.length_take,min_eq_left hd,result] using hh

def work (d : ℕ) (ws : List Word) := NativeSignedReturnStream.volume ws+(d+2)*ws.length

theorem stream_run (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length)
    (f g : ℤ → Fin 6) (p q : ℤ) :
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
    have hfirst := field_run_gap w d hw base g p q hb
    rw [hs] at hfirst
    have hnext := ih ht (putWord f p (DelimitedRadixRecord.field w))
      (putWord g q (DelimitedRadixRecord.field (result d w))) (p+w.length+1) (q+w.length+1)
    have hsrc : putWord (putWord f p (DelimitedRadixRecord.field w))
        (p+w.length+1) (NativeSignedReturnStream.encode ws)=putWord f p (NativeSignedReturnStream.encode (w::ws)) := by
      rw [show p+w.length+1=p+(DelimitedRadixRecord.field w).length by simp [DelimitedRadixRecord.field_length]; ring,
        putWord_append_forward,NativeSignedReturnStream.encode_cons]
    rw [hsrc] at hnext
    rw [show work d (w::ws)=w.length+d+3+work d ws by
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
    (f g : ℤ → Fin 6) (p q : ℤ)
    (hf : f (p+NativeSignedReturnStream.volume ws)=blank) :
    HoareTime program
      (fun v => v=tapes (putWord f p (NativeSignedReturnStream.encode ws)) g (clock d) p q 1)
      (fun v => v=tapes (putWord f p (NativeSignedReturnStream.encode ws))
        (putWord g q (NativeSignedReturnStream.encode (ws.map (result d)))) (clock d)
        (p+NativeSignedReturnStream.volume ws) (q+NativeSignedReturnStream.volume ws) 1) (work d ws) := by
  rintro v rfl
  refine ⟨work d ws,_,le_rfl,stream_run ws d hd f g p q,?_,rfl⟩
  have he : putWord f p (NativeSignedReturnStream.encode ws)
      (p+NativeSignedReturnStream.volume ws)=blank := by
    rw [putWord_outside f p (p+NativeSignedReturnStream.volume ws) _ (Or.inr (le_refl _))]
    exact hf
  simp [step,program,cfg,he]

theorem work_linear (ws : List Word) (d : ℕ) (hd : ∀ w∈ws,d≤w.length) :
    work d ws≤3*NativeSignedReturnStream.volume ws := by
  induction ws with
  | nil => simp [work,NativeSignedReturnStream.volume,NativeSignedReturnStream.encode]
  | cons w ws ih =>
    have hw := hd w (by simp)
    have ht := ih (by intro w h; exact hd w (by simp [h]))
    simp only [work,NativeSignedReturnStream.volume,NativeSignedReturnStream.encode_cons,
      List.length_append,DelimitedRadixRecord.field_length,List.length_cons] at *
    nlinarith

end IntegerMultBounds.Machine.NativeSignedGapScan
