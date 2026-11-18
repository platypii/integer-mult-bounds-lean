module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream

/-! Generate the residual mask and pivot queues on the same retained residue counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q A r d : ℕ} {P U : Type}

theorem controlStreams_exec (body : P → Pr P T Q A U)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = r*r) (mask pivot parents saved : Fin T)
    (maskRegs : (parents :: saved :: (slots rs ++ [mask])).Nodup)
    (pivotRegs : (parents :: saved :: (slots rs ++ [pivot])).Nodup) :
    ∃ prog, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ),
      0 < w → v.beforeH = B*prime^(r*(w*r)) →
      ∀ (u : HS T Q A U) (S : Stacks T A), ready (prime^(w-1)) S.R rs → S.R saved = [] →
      (S.R parents).length = v.beforeRows*v.rows*B →
      let bits := (LabelMask.selectors r w (LabelMask.records v)).map bitSymbol
      let R := Function.update S.R mask (bits ++ S.R mask)
      let schedules := (List.range (LabelMask.records v)).flatMap fun j =>
        let rows := classPivots (table (LabelStock.residue r w 1 j))
        scheduleCode rows ++ orderedScheduleCode (List.finRange d).reverse rows
      ∃ z n, z.user = u.user ∧ n ≤ 2*((v.beforeRows*v.rows*B)*(time (prime^(w-1)) (r*r) 1+5)+4) ∧
        Exec body prog (mk u S) n (mk z {S with R := Function.update R pivot (schedules ++ R pivot)}) := by
  obtain ⟨writeMask,maskRun⟩ := record_writes (body := body) r rs size mask parents saved maskRegs
  obtain ⟨writePivot,pivotRun⟩ := pivotRoundTrip_writes body table rs size pivot parents saved pivotRegs
  refine ⟨.seq writeMask writePivot,?_⟩
  intro v w B hw layout u S radix free count bits R schedules
  obtain ⟨y,l,hy,hl,emit⟩ := maskRun v w B hw layout u S ⟨radix,free,count⟩
  have hm := (List.nodup_cons.mp maskRegs).1
  have hs := (List.nodup_cons.mp (List.nodup_cons.mp maskRegs).2).1
  have slotsFree := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp maskRegs).2).2).2.2
  have same (k : Fin T) (hk : k ∈ slots rs) : R k = S.R k :=
    Function.update_of_ne (slotsFree k hk mask (by simp)) _ _
  have radix' : ready (prime^(w-1)) R rs := by
    intro pair h
    rw [same _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩),same _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩)]
    exact radix pair h
  have keepSaved : saved ≠ mask := by rintro rfl; exact hs (by simp)
  have keepParents : parents ≠ mask := by rintro rfl; exact hm (by simp)
  obtain ⟨z,n,hz,hn,write⟩ := pivotRun v w B hw layout y {S with R := R}
    ⟨radix',by simpa [R,keepSaved] using free,by simpa [R,keepParents] using count⟩
  exact ⟨z,l+n,hz.trans hy,by omega,.seq emit write⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
