import IntegerMultBounds.Machine.BinaryDescriptorStackRoundtrip
import IntegerMultBounds.Machine.GrowingCounterData
import IntegerMultBounds.Machine.ExactFrame

/-! Physically remove high zero bits from a marked binary word and return its
head to one. The fixed control discovers all boundaries by reading symbols. -/
namespace IntegerMultBounds.Machine.BinaryCanonicalTrim
open BinaryDescriptorStack (descriptor)
variable {a : ℕ}

/-- Every binary word splits into its canonical prefix and high zero padding. -/
theorem canonical_split (xs : List Bool) :
    ∃ ys : List Bool, ∃ n : ℕ, xs = ys ++ List.replicate n false ∧ GrowingCounterData.Canonical ys := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[],0,rfl,Or.inl rfl⟩
  | append_singleton xs b ih =>
    cases b
    · obtain ⟨ys,n,he,hc⟩ := ih
      refine ⟨ys,n+1,?_,hc⟩
      rw [he,List.replicate_add]
      simp [List.append_assoc]
    · refine ⟨xs++[true],0,by simp,Or.inr ?_⟩
      simp

theorem value_padding (ys : List Bool) (n : ℕ) :
    Counter.value (ys++List.replicate n false) = Counter.value ys := by
  induction ys with
  | nil =>
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.nil_append,Counter.value] at ih
      simp [List.replicate_succ,Counter.value,ih]
  | cons b ys ih => simp [Counter.value,ih]

def trim : Program 1 1 a where
  tapes_pos := by decide
  start := 0
  transition := fun _ sy => if sy 0 = bitSymbol false then some (0,fun _ => (blank,Move.left)) else none

private def cfg (f : ℤ → Fin (a+4)) (p : ℤ) : Config 1 1 a := ⟨0,fun _ => p,fun _ => f⟩

def pad (f : ℤ → Fin (a+4)) (p : ℤ) : ℕ → ℤ → Fin (a+4)
  | 0 => f
  | n+1 => Function.update (pad f p n) (p+n) (bitSymbol false)

private theorem pad_outside (f : ℤ → Fin (a+4)) (p z : ℤ) (n : ℕ)
    (hz : z < p ∨ p+n ≤ z) : pad f p n z = f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : z ≠ p+n := by omega
    simp only [pad,Function.update_of_ne hn]
    exact ih (by omega)

private theorem trim_step (f : ℤ → Fin (a+4)) (p : ℤ) (hf : f p = bitSymbol false) :
    step trim (cfg f p) = some (cfg (Function.update f p blank) (p-1)) := by
  simp only [step,trim,cfg,hf,ite_true,Move.offset]
  congr 1
  congr 1
  funext i z; simp [Function.update_apply,eq_comm]

private theorem trim_run (f : ℤ → Fin (a+4)) (p : ℤ) (n : ℕ)
    (hf : ∀ z, p ≤ z → f z = blank) :
    run trim n (cfg (pad f p n) (p+n-1)) = some (cfg f (p-1)) := by
  induction n with
  | zero => simp [run,pad]
  | succ n ih =>
    have hcoord : p+(n+1 : ℕ)-1 = p+n := by omega
    rw [hcoord]
    have hs := trim_step (pad f p (n+1)) (p+n) (by simp [pad])
    have he : Function.update (pad f p (n+1)) (p+n) blank = pad f p n := by
      rw [pad,Function.update_idem]
      apply Function.update_eq_self_iff.mpr
      rw [pad_outside _ _ _ _ (Or.inr le_rfl),hf _ (by omega)]
    rw [he] at hs
    simp only [run,hs,Option.bind_some]
    exact ih

private theorem descriptor_pad (ys : List Bool) (n : ℕ) :
    descriptor (a := a) (ys++List.replicate n false) = pad (descriptor ys) (1+ys.length) n := by
  induction n with
  | zero => simp [pad]
  | succ n ih =>
    rw [show List.replicate (n+1) false = List.replicate n false ++ [false] by simp [List.replicate_add]]
    rw [← List.append_assoc]
    change putWord BinaryDescriptorStack.empty 1 ((ys++List.replicate n false++[false]).map bitSymbol) = _
    rw [List.map_append,← putWord_append_forward]
    simp only [List.map_singleton,List.length_map,List.length_append,List.length_replicate,putWord]
    change Function.update (descriptor (ys++List.replicate n false)) (1+(ys.length+n : ℕ)) (bitSymbol false) = _
    rw [ih]
    simp only [pad,Nat.cast_add,add_assoc]

private theorem descriptor_after (ys : List Bool) (z : ℤ) (hz : 1+ys.length ≤ z) :
    descriptor (a := a) ys z = blank := by
  rw [descriptor,putWord_outside _ _ _ _ (Or.inr (by simpa using hz))]
  simp [BinaryDescriptorStack.empty,show z ≠ 0 by omega]

private theorem descriptor_last (ys : List Bool) (hc : GrowingCounterData.Canonical ys) :
    descriptor (a := a) ys ys.length ≠ bitSymbol false := by
  rcases hc with rfl | hc
  · simp [descriptor,BinaryDescriptorStack.empty,putWord,separator,bitSymbol,Fin.ext_iff]
  · obtain ⟨zs,rfl⟩ := List.getLast?_eq_some_iff.mp hc
    rw [descriptor,List.map_append,← putWord_append_forward]
    simp [List.length_map,List.length_append,putWord,bitSymbol,Fin.ext_iff,add_comm]

def one (xs : List Bool) (p : ℤ) : Tapes 1 a := ⟨fun _ => p,fun _ => descriptor xs⟩

theorem trim_hoare (ys : List Bool) (n : ℕ) (hc : GrowingCounterData.Canonical ys) :
    HoareTime (trim (a := a)) (fun v => v = one (ys++List.replicate n false) (ys.length+n))
      (fun v => v = one ys ys.length) n := by
  have hr := trim_run (descriptor (a := a) ys) (1+ys.length) n
    (fun z hz => descriptor_after ys z hz)
  have hp : (1 : ℤ)+ys.length+n-1 = ys.length+n := by omega
  have hq : (1 : ℤ)+ys.length-1 = ys.length := by omega
  rw [← descriptor_pad,hp,hq] at hr
  rintro v rfl
  refine ⟨n,cfg (descriptor ys) ys.length,le_rfl,hr,?_,rfl⟩
  simp [step,trim,cfg,descriptor_last ys hc]

/-- Four fixed states trim zeros, rewind to the marker, and step to cell one. -/
def program : Program 1 4 a := seq (seq trim (Rewind.program separator)) StepRight.program

theorem normalize_hoare (ys : List Bool) (n : ℕ) (hc : GrowingCounterData.Canonical ys) :
    HoareTime (program (a := a)) (fun v => v = one (ys++List.replicate n false) (ys.length+n))
      (fun v => v = one ys 1) (ys.length+n+3) := by
  have hr := Rewind.rewind_hoare (separator : Fin (a+4)) (descriptor ys) ys.length ys.length
    (by
      intro j hj
      have hz : 1 ≤ (ys.length : ℤ)-j ∧ (ys.length : ℤ)-j < 1+ys.length := by omega
      have hm := ReturnOrigin.putWord_mem BinaryDescriptorStack.empty 1 (ys.map (bitSymbol (a := a))) ((ys.length : ℤ)-j) (by simpa using hz)
      obtain ⟨b,_,he⟩ := List.mem_map.mp hm
      change descriptor ys ((ys.length : ℤ)-j) ≠ separator
      rw [descriptor,← he]
      cases b <;> simp [bitSymbol,separator,Fin.ext_iff])
    (by rw [sub_self,descriptor,putWord_outside _ _ _ _ (Or.inl (by omega))]; rfl)
  simp only [sub_self] at hr
  have hh := ((trim_hoare (a := a) ys n hc).seq hr).seq (StepRight.step_hoare (descriptor ys) 0)
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- Every input has an actual canonical output of the same value. -/
theorem normalize_exists (xs : List Bool) :
    ∃ ys : List Bool, GrowingCounterData.Canonical ys ∧ Counter.value ys = Counter.value xs ∧
      ys.length ≤ xs.length ∧
      HoareTime (program (a := a)) (fun v => v = one xs xs.length)
        (fun v => v = one ys 1) (xs.length+3) := by
  obtain ⟨ys,n,rfl,hc⟩ := canonical_split xs
  refine ⟨ys,hc,(value_padding ys n).symm,by simp,?_⟩
  simpa only [List.length_append,List.length_replicate,Nat.cast_add] using normalize_hoare (a := a) ys n hc

end IntegerMultBounds.Machine.BinaryCanonicalTrim
