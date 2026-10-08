import IntegerMultBounds.Machine.MarkedWordCleanup
import IntegerMultBounds.Machine.CountedCopyReuse

/-! Erase a marked binary descriptor and remove its sentinel. The entire tape
returns to blank at head zero, ready for a converter that installs fresh markers. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorReset

open MarkedWordCleanup (one empty)

def bank (bs : List Bool) : Tapes 1 0 := one (CountedCopyReuse.binary bs) 1

private theorem binary_word (bs : List Bool) :
    CountedCopyReuse.binary bs = MarkedWordCleanup.marked (bs.map bitSymbol) := by
  have h (f : ℤ → Fin 4) (p : ℤ) (xs : List Bool) : putBits f p xs = putWord f p (xs.map bitSymbol) := by
    induction xs generalizing p with
    | nil => rfl
    | cons x xs ih => simp only [putBits,putWord,List.map_cons,ih]
  exact h _ _ _

/-- Four fixed states: clear forward, rewind to sentinel, erase sentinel. -/
def program : Program 1 4 0 :=
  seq (seq MarkedWordCleanup.clearProgram (Rewind.program separator)) MarkedWordCleanup.unmarkProgram

theorem reset_hoare (bs : List Bool) :
    HoareTime program (fun v => v = bank bs) (fun v => v = one (fun _ => blank) 0)
      (2*bs.length+4) := by
  have hb : ∀ b ∈ bs.map bitSymbol, b ≠ (blank : Fin 4) := by
    intro b hh
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hh
    cases x <;> decide
  have hc := MarkedWordCleanup.clear_hoare (bs.map bitSymbol) hb
  simp only [List.length_map,← binary_word] at hc
  have hr := Rewind.rewind_hoare (separator : Fin 4) empty (bs.length+1) (bs.length+1)
    (by intro j hj; simp [empty,show (bs.length:ℤ)+1-j ≠ 0 by omega,blank,separator])
    (by simp [empty])
  have hr' : HoareTime (Rewind.program (separator : Fin 4))
      (fun v => v = one empty (1+bs.length)) (fun v => v = one empty 0) (bs.length+1) := by
    simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using hr
  exact ((hc.seq hr').seq (MarkedWordCleanup.unmark_hoare [])).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.BinaryDescriptorReset
