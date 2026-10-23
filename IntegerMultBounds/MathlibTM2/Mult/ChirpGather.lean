module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Copy one overlapping window and advance the shared source

The row accumulator stores reversed symbol streams. A single final reversal will put
all rows in their original order. Consumed source symbols are saved for one final
restoration; copying a window itself leaves the source intact.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def gatherNext (window advance src acc current savedSource buf tmp : Fin T) : Pr P T Q A U :=
  .seq (copyPrefix window src current buf tmp)
    (.seq (moveR current acc id) (transfer advance src savedSource tmp))

/-- Exact tape execution for a window and its next forward advance, with arbitrary tails. -/
theorem gatherNext_exec {window advance src acc current savedSource buf tmp : Fin T}
    (hreg : [window, advance, src, acc, current, savedSource, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs tail ds rest : List (Fin (A + 4)))
    (hwindow : S.R src = xs ++ tail) (hadvance : S.R src = ds ++ rest)
    (hw : (S.R window).length = xs.length) (hd : (S.R advance).length = ds.length)
    (hcurrent : S.R current = []) (hbuf : S.R buf = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (gatherNext window advance src acc current savedSource buf tmp) (mk v S)
        (12 * xs.length + 4 * ds.length + 16)
        (mk v' { S with R := (Function.update (Function.update
          (Function.update S.R src rest) savedSource (ds.reverse ++ S.R savedSource))
          acc (xs.reverse ++ S.R acc)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := copyPrefix_exec (body := body)
    (show [window, src, current, buf, tmp].Nodup by simp_all)
    v S xs tail hwindow hw hbuf htmp
  set S₁ : Stacks T A := { S with R := Function.update S.R current (xs ++ S.R current) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body current acc ‹acc ≠ current›.symm id v₁ S₁
  set S₂ : Stacks T A := { S₁ with R := movedR S₁.R current acc id (S₁.R current) }
  have frame (k : Fin T) (hc : k ≠ current) (ha : k ≠ acc) : S₂.R k = S.R k := by
    simp [S₂, S₁, movedR, hc, ha]
  obtain ⟨v₃, hu₃, he₃⟩ := transfer_exec (body := body)
    (show [advance, src, savedSource, tmp].Nodup by simp_all) v₂ S₂ ds rest
    (by rw [frame _ ‹src ≠ current› ‹src ≠ acc›]; exact hadvance)
    (by rw [frame _ ‹advance ≠ current› ‹advance ≠ acc›]; exact hd)
    (by rw [frame _ ‹current ≠ tmp›.symm ‹acc ≠ tmp›.symm]; exact htmp)
  refine ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp only [S₁, Function.update_self, hcurrent, List.append_nil]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    simp only [S₂, S₁, movedR, Function.update_apply, List.map_id, hcurrent, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
