import IntegerMultBounds.Machine.NativePolynomialConjugationData
import IntegerMultBounds.Machine.Negate
import IntegerMultBounds.Machine.ReturnOrigin
import IntegerMultBounds.Machine.NativeZeroPaddingArray

/-! A fixed one-tape three-state scan conjugates native polynomial records
in place. It skips real fields, negates imaginary two's-complement fields,
retains every separator and restores the stream head with no private tapes. -/
namespace IntegerMultBounds.Machine.NativePolynomialConjugation
noncomputable section
open NativePolynomialConjugationData (digit digits bits negative coefficient array digits_bits)
open ButterflyStreamData (Coefficient encoded)
open RadixDigits (digitSymbol)

def delta (s : Fin 3) (x : Fin 6) : Fin 3 × Fin 6 :=
  if x=separator then (if s=0 then 1 else 0,x)
  else if s=2 then (2,if x=digitSymbol (0 : Fin 2) then digitSymbol (1 : Fin 2) else digitSymbol (0 : Fin 2))
  else if s=1 then (if x=digitSymbol (0 : Fin 2) then 1 else 2,x)
  else (0,x)

def scanProgram : Program 1 3 2 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if sy 0=blank then none
    else some ((delta s (sy 0)).1,fun _ => ((delta s (sy 0)).2,.right))

def cfg (f : ℤ → Fin 6) (p : ℤ) (s : Fin 3) : Config 1 3 2 :=
  ⟨s,fun _ => p,fun _ => f⟩

def scan : Fin 3 → List (Fin 6) → Fin 3 × List (Fin 6)
  | s, [] => (s,[])
  | s, x::xs =>
    let d := delta s x
    let r := scan d.1 xs
    (r.1,d.2::r.2)

theorem scan_length (s : Fin 3) (xs : List (Fin 6)) : (scan s xs).2.length=xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [scan,List.length_cons,ih]

theorem data_step (f : ℤ → Fin 6) (p : ℤ) (s : Fin 3) (x : Fin 6)
    (hx : f p=x) (hn : x≠blank) :
    step scanProgram (cfg f p s)=some
      (cfg (Function.update f p (delta s x).2) (p+1) (delta s x).1) := by
  simp only [step,scanProgram,cfg,hx,hn,↓reduceIte,Move.offset]
  congr 1
  congr 1
  funext i j
  simp only [Function.update_apply]
  rfl

theorem scan_run (f : ℤ → Fin 6) (p : ℤ) (s : Fin 3) (xs : List (Fin 6))
    (hn : ∀ x∈xs,x≠blank) :
    run scanProgram xs.length (cfg (putWord f p xs) p s)=
      some (cfg (putWord f p (scan s xs).2) (p+xs.length) (scan s xs).1) := by
  induction xs generalizing f p s with
  | nil => simp [scan,run]
  | cons x xs ih =>
    rw [List.length_cons,add_comm,run_add,run_one,
      data_step _ _ s x (putWord_head _ _ _ _) (hn x (by simp))]
    simp only [Option.bind_some,putWord_replace_head]
    rw [ih _ _ _ (fun y hy => hn y (by simp [hy]))]
    simp only [scan,putWord_cons,Nat.cast_add,Nat.cast_one]
    congr 2
    ring

theorem scan_real (bs : List Bool) (tail : List (Fin 6)) :
    scan 0 ((digits bs).map digitSymbol++[separator]++tail)=
      ((scan 1 tail).1,((digits bs).map digitSymbol++[separator])++(scan 1 tail).2) := by
  induction bs with
  | nil => simp [digits,scan,delta,separator]
  | cons b bs ih =>
      have hh := congrArg Prod.fst ih
      have ht := congrArg Prod.snd ih
      cases b <;> simp [digits,digit,scan,delta,separator,digitSymbol,List.append_assoc] at * <;>
        exact ⟨hh,ht⟩

theorem scan_imag (seen : Bool) (bs : List Bool) (tail : List (Fin 6)) :
    scan (if seen then 2 else 1) ((digits bs).map digitSymbol++[separator]++tail)=
      ((scan 0 tail).1,((digits (Negate.negFrom seen bs)).map digitSymbol++[separator])++(scan 0 tail).2) := by
  induction bs generalizing seen with
  | nil => cases seen <;> simp [digits,scan,delta,separator,Negate.negFrom]
  | cons b bs ih =>
    have hf := ih false
    have ht := ih true
    have hf1 := congrArg Prod.fst hf
    have hf2 := congrArg Prod.snd hf
    have ht1 := congrArg Prod.fst ht
    have ht2 := congrArg Prod.snd ht
    simp [digits,separator,List.append_assoc] at hf1 hf2 ht1 ht2
    cases seen <;> cases b <;>
      simp [digits,digit,scan,delta,separator,digitSymbol,Negate.negFrom,List.append_assoc] <;>
      first | exact ⟨hf1,hf2⟩
            | exact ⟨ht1,ht2⟩

theorem scan_record (x : Coefficient) (tail : List (Fin 6)) :
    scan 0 (encoded x++tail)=((scan 0 tail).1,encoded (coefficient x)++(scan 0 tail).2) := by
  have hr := scan_real (bits x.1) ((digits (bits x.2)).map digitSymbol++[separator]++tail)
  rw [digits_bits,digits_bits] at hr
  have hi := scan_imag false (bits x.2) tail
  simp only [Bool.false_eq_true,↓reduceIte,Negate.negFrom_false,digits_bits] at hi
  rw [hi] at hr
  simpa only [encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,
    coefficient,negative,List.append_assoc] using hr

def records (xs : List Coefficient) := (xs.map encoded).flatten

theorem scan_records (xs : List Coefficient) :
    scan 0 (records xs)=(0,records (xs.map coefficient)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [records,List.map_cons,List.flatten_cons] at *
    rw [scan_record,ih]

theorem records_nonblank (xs : List Coefficient) (x : Fin 6) (hx : x∈records xs) : x≠blank := by
  simp only [records,List.mem_flatten] at hx
  obtain ⟨ys,hy,hx⟩ := hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
  simp only [encoded,DelimitedRadixRecord.complex,DelimitedRadixRecord.field,List.mem_append,
    List.mem_map,List.mem_singleton] at hx
  rcases hx with (⟨d,_,rfl⟩|rfl)|(⟨d,_,rfl⟩|rfl)
  all_goals intro h; have hv := congrArg Fin.val h
  all_goals simp only [digitSymbol,separator,blank] at hv
  all_goals omega

def program := seq scanProgram (ReturnOrigin.program (a:=2))
def bank (xs : List Coefficient) := (cfg (putWord (fun _ => blank) 0 (records xs)) 0 0).tapes

theorem runs (xs : List Coefficient) :
    HoareTime program (fun v => v=bank xs) (fun v => v=bank (xs.map coefficient))
      (2*(records xs).length+3) := by
  have hs : HoareTime scanProgram (fun v => v=bank xs)
      (fun v => v=(cfg (putWord (fun _ => blank) 0 (records (xs.map coefficient))) (records xs).length 0).tapes)
      (records xs).length := by
    rintro v rfl
    have hrun := scan_run (fun _ => blank) 0 0 (records xs) (records_nonblank xs)
    rw [scan_records] at hrun
    refine ⟨_,_,le_rfl,hrun,?_,by simp only [cfg,Config.tapes,zero_add]⟩
    have he : (records (xs.map coefficient)).length=(records xs).length := by
      have h := scan_length 0 (records xs)
      rw [scan_records] at h
      exact h
    simp only [step,scanProgram,cfg]
    rw [putWord_outside _ _ _ _ (Or.inr (by simp [he]))]
    rfl
  have he : (records (xs.map coefficient)).length=(records xs).length := by
    have h := scan_length 0 (records xs)
    rw [scan_records] at h
    exact h
  have hr := ReturnOrigin.return_hoare (records (xs.map coefficient)) (records_nonblank _)
  rw [he] at hr
  exact (hs.seq hr).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.NativePolynomialConjugation
