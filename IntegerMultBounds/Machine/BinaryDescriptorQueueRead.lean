import IntegerMultBounds.Machine.BinaryDescriptorQueueEmit
import IntegerMultBounds.Machine.MarkedWordCleanup
import IntegerMultBounds.Machine.RawLinearCombinationCleanup

/-! Read one forward binary field into a fresh marked descriptor. The actual
next separator stops the copy machine, source cells are retained literally,
and both cursors are moved/rewound by paid transitions. -/
namespace IntegerMultBounds.Machine.BinaryDescriptorQueueRead
noncomputable section
open MarkedWordCleanup (one empty marked)
open RawLinearCombinationCleanup (prepend prepend_runs)
variable {a : ℕ}

def rightProgram : Program 2 2 a := DescriptorStackControl.once (by decide)
  (fun sy i => (sy i,Move.right))

private theorem right_runs (f g : ℤ → Fin (a+4)) (p r : ℤ) :
    HoareTime rightProgram (fun v => v=Copy.tapes f g p r)
      (fun v => v=Copy.tapes f g (p+1) (r+1)) 1 := by
  apply (DescriptorStackControl.once_hoare (by decide) _ (Copy.tapes f g p r)).consequence
    (fun _ h => h) _ le_rfl
  rintro v rfl
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i z
    fin_cases i
    · by_cases hz : z=p <;> simp [Copy.tapes,Copy.cfg,Config.tapes,hz]
    · by_cases hz : z=r <;> simp [Copy.tapes,Copy.cfg,Config.tapes,hz]

private theorem marker (xs : List Bool) : marked (a := a) (xs.map bitSymbol) 0=separator := by
  rw [marked,putWord_outside _ _ _ _ (Or.inl (by omega))]
  rfl

private theorem no_marker (xs : List Bool) (z : ℤ) (hz : 0 < z) :
    marked (a := a) (xs.map bitSymbol) z≠separator := by
  by_cases hi : z < 1+xs.length
  · have hm := ReturnOrigin.putWord_mem empty 1 (xs.map (bitSymbol (a := a))) z
      ⟨by omega,by simpa using hi⟩
    obtain ⟨b,_,hb⟩ := List.mem_map.mp hm
    change putWord empty 1 (xs.map bitSymbol) z≠separator
    rw [← hb]
    cases b <;> simp [bitSymbol,separator,Fin.ext_iff]
  · rw [marked,putWord_outside _ _ _ _ (Or.inr (by simpa using le_of_not_gt hi))]
    simp [empty,show z≠0 by omega,blank,separator,Fin.ext_iff]

private theorem rewind_runs (xs : List Bool) :
    HoareTime (Rewind.program (separator : Fin (a+4)))
      (fun v => v=one (marked (xs.map bitSymbol)) (1+xs.length))
      (fun v => v=one (marked (xs.map bitSymbol)) 0) (xs.length+1) := by
  have h := Rewind.rewind_hoare (separator : Fin (a+4)) (marked (xs.map bitSymbol))
    (xs.length+1) (xs.length+1)
    (by intro j hj; apply no_marker; omega) (by simpa using marker (a := a) xs)
  simpa only [Rewind.cfg,Config.tapes,one,sub_self,Nat.cast_add,Nat.cast_one,add_comm] using h

def program : Program 2 6 a :=
  seq (seq (seq (prepend MarkedWordCleanup.markProgram 1) (Copy.program separator false))
    (prepend (Rewind.program separator) 1)) rightProgram

/-- The source field itself is read; only its next delimiter is required.
The finite program knows neither its bit length nor its numeric value. -/
theorem runs (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool)
    (he : f (p+xs.length)=separator) :
    HoareTime program
      (fun v => v=Copy.tapes (putWord f p (xs.map bitSymbol)) (fun _ => blank) p 0)
      (fun v => v=Copy.tapes (putWord f p (xs.map bitSymbol)) (BinaryDescriptorStack.descriptor xs)
        (p+xs.length+1) 1) (2*xs.length+6) := by
  have hm := prepend_runs MarkedWordCleanup.markProgram _ _
    (one (putWord f p (xs.map bitSymbol)) p) (MarkedWordCleanup.mark_hoare [])
  have hc := Copy.copy_hoare (separator : Fin (a+4)) false f empty p 1 (xs.map bitSymbol)
    (by intro z hz; obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz; cases b <;> simp [bitSymbol,separator,Fin.ext_iff])
    (by simpa using he)
  have hid : (Copy.retained false : Fin (a+4) → Fin (a+4))=id := by funext x; rfl
  simp only [hid,List.map_id,List.length_map] at hc
  have hr := prepend_runs (Rewind.program (separator : Fin (a+4))) _ _
    (one (putWord f p (xs.map bitSymbol)) (p+xs.length)) (rewind_runs (a := a) xs)
  have hf := right_runs (putWord f p (xs.map bitSymbol)) (marked (xs.map bitSymbol)) (p+xs.length) 0
  have ha : ∀ (u v : ℤ → Fin (a+4)) (j k : ℤ), (one u j).append (one v k)=Copy.tapes u v j k := by
    intro u v j k
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [ha,ha] at hm hr
  exact (((hm.seq hc).seq hr).seq hf).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.BinaryDescriptorQueueRead
