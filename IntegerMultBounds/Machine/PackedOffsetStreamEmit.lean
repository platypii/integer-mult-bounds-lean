import IntegerMultBounds.Machine.BinaryOffsetStreamRead
import IntegerMultBounds.Machine.DescriptorStackControl
import IntegerMultBounds.Machine.ExactFrame

/-! Move one marked binary word to a raw stream, write its blank delimiter,
and erase the scratch marker. The fixed machine returns scratch wholly blank. -/
namespace IntegerMultBounds.Machine.PackedOffsetStreamEmit
open MarkedWordCleanup (empty one)
open CountedCopyReuse (binary)

def encoded (xs : List Bool) : List (Fin 4) := xs.map bitSymbol++[blank]

def first {s : ℕ} (M : Program 1 s 0) := extend M 1

theorem first_hoare {s cost : ℕ} (M : Program 1 s 0) (f h : ℤ → Fin 4) (p r : ℤ)
    (hh : HoareTime M (fun v => v = one f p) (fun v => v = one h r) cost)
    (g : ℤ → Fin 4) (q : ℤ) :
    HoareTime (first M) (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes h g r q) cost := by
  have he (f g : ℤ → Fin 4) (p q : ℤ) : (one f p).append (one g q) = Copy.tapes f g p q := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  simpa only [he,first] using hoare_extend_eq hh (one g q)

def delimiter : Program 2 2 0 := DescriptorStackControl.once (by decide)
  (fun sy i => if i = 0 then (sy i,Move.stay) else (blank,Move.right))

theorem delimiter_hoare (f g : ℤ → Fin 4) (p q : ℤ) :
    HoareTime delimiter (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes f (Function.update g q blank) p (q+1)) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (Copy.tapes f g p q)).consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes,Move.offset]
  · funext i z
    fin_cases i
    · simp [Copy.tapes,Copy.cfg,Config.tapes]
      intro h; subst z; rfl
    · simp [Copy.tapes,Copy.cfg,Config.tapes,Function.update_apply]

private theorem erased (f : ℤ → Fin 4) (p : ℤ) (xs : List (Fin 4))
    (hf : ∀ z, p ≤ z → f z = blank) : putWord f p (xs.map (Copy.retained true)) = f := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,putWord,Copy.retained,ite_true]
    rw [ih (p+1) (fun z hz => hf z (by omega))]
    exact Function.update_eq_self_iff.mpr (hf p le_rfl).symm

def program : Program 2 6 0 := seq (seq (seq (Copy.program blank true)
  (first (Rewind.program separator))) (first MarkedWordCleanup.unmarkProgram)) delimiter

theorem emits (xs : List Bool) (g : ℤ → Fin 4) (q : ℤ) :
    HoareTime program (fun v => v = Copy.tapes (binary xs) g 1 q)
      (fun v => v = Copy.tapes (fun _ => blank) (putWord g q (encoded xs)) 0 (q+(encoded xs).length))
      (2*xs.length+6) := by
  have hc := Copy.copy_hoare (blank : Fin 4) true empty g 1 q (xs.map bitSymbol)
    (by intro x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx; cases b <;> decide)
    (by simp [empty,show (1 : ℤ)+xs.length ≠ 0 by omega])
  rw [erased empty 1 _ (by intro z hz; simp [empty,show z ≠ 0 by omega])] at hc
  rw [show putWord empty 1 (xs.map bitSymbol) = binary xs from (BinaryOffsetStreamRead.binary_word xs).symm] at hc
  simp only [List.length_map] at hc
  have hr := Rewind.rewind_hoare (separator : Fin 4) empty (1+xs.length) (xs.length+1)
    (by intro j hj; simp [empty,show (1 : ℤ)+xs.length-j ≠ 0 by omega,blank,separator])
    (by rw [show (1 : ℤ)+xs.length-(xs.length+1 : ℕ) = 0 by omega]; rfl)
  have hr' : HoareTime (Rewind.program (separator : Fin 4))
      (fun v => v = one empty (1+xs.length)) (fun v => v = one empty 0) (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,show (1 : ℤ)+xs.length-(xs.length+1 : ℕ) = 0 by omega] using hr
  have h₁ := first_hoare _ _ _ _ _ hr' (putWord g q (xs.map bitSymbol)) (q+xs.length)
  have h₂ := first_hoare _ _ _ _ _ (MarkedWordCleanup.unmark_hoare ([] : List (Fin 4)))
    (putWord g q (xs.map bitSymbol)) (q+xs.length)
  have h₃ := delimiter_hoare (fun _ => blank) (putWord g q (xs.map bitSymbol)) 0 (q+xs.length)
  have he : Function.update (putWord g q (xs.map bitSymbol)) (q+xs.length) blank = putWord g q (encoded xs) := by
    rw [encoded,← putWord_append_forward]
    simp only [List.length_map,putWord]
  rw [he] at h₃
  apply (((hc.seq h₁).seq h₂).seq h₃).consequence (fun _ h => h) _ (by omega)
  intro v hv
  simpa only [encoded,List.length_append,List.length_map,List.length_singleton,Nat.cast_add,Nat.cast_one,add_assoc] using hv

end IntegerMultBounds.Machine.PackedOffsetStreamEmit
