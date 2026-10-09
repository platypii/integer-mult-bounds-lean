import IntegerMultBounds.Machine.BinaryDescriptorReset
import IntegerMultBounds.Machine.Placement

/-! Consume one blank-delimited binary word from a retained control stream.
The previous marked offset is erased before copying; its marker is physically
reinstalled, its head restored, and the stream delimiter is crossed. -/
namespace IntegerMultBounds.Machine.BinaryOffsetStreamRead
open CountedCopyReuse (binary)
open MarkedWordCleanup (one empty marked)

def target {s : ℕ} (M : Program 1 s 0) : Program 2 s 0 :=
  Placement.placed M (Equiv.swap 0 1 : Fin (1+1) ≃ Fin 2)

theorem target_hoare {s cost : ℕ} (M : Program 1 s 0)
    (g h : ℤ → Fin 4) (q r : ℤ)
    (hh : HoareTime M (fun v => v = one g q) (fun v => v = one h r) cost)
    (f : ℤ → Fin 4) (p : ℤ) :
    HoareTime (target M) (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes f h p r) cost := by
  have ha : Placement.active (Equiv.swap 0 1 : Fin (1+1) ≃ Fin 2)
      (Copy.tapes f g p q) = one g q := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have ht := Placement.hoare_at hh (Equiv.swap 0 1 : Fin (1+1) ≃ Fin 2) _ ha
  apply ht.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def advance : Program 2 2 0 where
  tapes_pos := by decide
  start := 0
  transition := fun s sy => if s = 0 then some (1,fun i => (sy i,.right)) else none

theorem advance_hoare (f g : ℤ → Fin 4) (p q : ℤ) :
    HoareTime advance (fun v => v = Copy.tapes f g p q)
      (fun v => v = Copy.tapes f g (p+1) (q+1)) 1 := by
  rintro v rfl
  refine ⟨1,⟨1,(Copy.tapes f g (p+1) (q+1)).head,(Copy.tapes f g (p+1) (q+1)).tape⟩,
    le_rfl,?_,?_,rfl⟩
  · simp only [run_one,step,advance,Tapes.start,ite_true,Move.offset]
    congr 1
    congr 1
    · funext i; fin_cases i <;> rfl
    · funext i z; fin_cases i <;> simp [Copy.tapes,Copy.cfg,Config.tapes] <;>
        intro h <;> subst z <;> rfl
  · simp [step,advance]

theorem binary_word (xs : List Bool) : binary xs = marked (xs.map bitSymbol) := by
  have he (f : ℤ → Fin 4) (p : ℤ) : putBits f p xs = putWord f p (xs.map bitSymbol) := by
    induction xs generalizing f p with
    | nil => rfl
    | cons x xs ih => simp only [putBits,putWord,List.map_cons,ih]
  exact he _ _

theorem binary_marker (xs : List Bool) : binary xs 0 = separator := by
  rw [binary,putBits_outside _ _ _ _ (Or.inl (by omega))]
  rfl

theorem binary_ne_marker (xs : List Bool) (j : ℤ) (hj : 0 < j) : binary xs j ≠ separator := by
  by_cases hh : j < 1+xs.length
  · exact putBits_ne_separator CountedCopyReuse.empty 1 j xs (by omega) hh
  · rw [binary,putBits_outside _ _ _ _ (Or.inr (by omega))]
    simp [CountedCopyReuse.empty,ne_of_gt hj,blank,separator]

def program : Program 2 10 0 :=
  seq (seq (seq (seq (target BinaryDescriptorReset.program)
    (target MarkedWordCleanup.markProgram)) (Copy.program blank false))
    (target (Rewind.program separator))) advance

/-- Only the next literal source segment and its delimiter are required;
all other source cells, including later control words, survive unchanged. -/
theorem reads (f : ℤ → Fin 4) (p : ℤ) (old xs : List Bool)
    (hend : f (p+xs.length) = blank) :
    HoareTime program
      (fun v => v = Copy.tapes (putWord f p (xs.map bitSymbol)) (binary old) p 1)
      (fun v => v = Copy.tapes (putWord f p (xs.map bitSymbol)) (binary xs) (p+xs.length+1) 1)
      (2*old.length+2*xs.length+11) := by
  let src := putWord f p (xs.map bitSymbol)
  have h₀ := target_hoare BinaryDescriptorReset.program _ _ 1 0
    (BinaryDescriptorReset.reset_hoare old) src p
  have h₁ := target_hoare MarkedWordCleanup.markProgram _ _ 0 1
    (MarkedWordCleanup.mark_hoare ([] : List (Fin 4))) src p
  have hnb : ∀ x ∈ xs.map bitSymbol, x ≠ (blank : Fin 4) := by
    intro x hx
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
    cases b <;> decide
  have h₂ := Copy.copy_hoare (blank : Fin 4) false f empty p 1 (xs.map bitSymbol) hnb
    (by simpa using hend)
  have hid : (Copy.retained false : Fin 4 → Fin 4) = id := rfl
  simp only [hid,List.map_id,List.length_map] at h₂
  rw [show putWord empty 1 (xs.map bitSymbol) = binary xs from (binary_word xs).symm] at h₂
  have hr := Rewind.rewind_hoare (separator : Fin 4) (binary xs) (1+xs.length) (xs.length+1)
    (by intro j hj; exact binary_ne_marker xs _ (by omega))
    (by convert binary_marker xs using 1; congr 1; omega)
  have hr' : HoareTime (Rewind.program (separator : Fin 4))
      (fun v => v = one (binary xs) (1+xs.length)) (fun v => v = one (binary xs) 0)
      (xs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,show (1:ℤ)+xs.length-(xs.length+1 : ℕ) = 0 by omega] using hr
  have h₃ := target_hoare (Rewind.program separator) _ _ _ _ hr' src (p+xs.length)
  have h₄ := advance_hoare src (binary xs) (p+xs.length) 0
  exact ((((h₀.seq h₁).seq h₂).seq h₃).seq h₄).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.BinaryOffsetStreamRead
