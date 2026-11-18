module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRewind
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearReady

/-! Expose the preceding matrix on the alternate archive without moving the payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {P U α : Type} {T Q A d b w W : ℕ} [NeZero (b^(w+1))]
local notation "M" => b^(w+1)

theorem advanceArchive_exec (bank next : Fin 35 ↪ Fin T)
    (fixed : ∀ i, i ≠ 34 → next i = bank i)
    (body : P → Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A)
    (H J : ℕ) (m newer older : Matrix (Fin d) (Fin d) (ZMod M))
    (tail rest : List (Fin (A+4))) (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (original : Fin (M^d*W) → α) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (ready : ColumnReady bank H J m tail sym source dest p q original addr S)
    (archive : S.R (next 34) = matrixWords A H newer ++ matrixWords A H older ++ rest) :
    let F := {S with R := Function.update S.R (next 34) (matrixWords A H older ++ rest)}
    ∃ z, z.user = v.user ∧ Exec body (dropWords (bank 2) (next 34) (bank 0) (d*d))
      (mk v S) (d*d*(4*H+4)+1) (mk z F) ∧
      ColumnReady next H J older rest sym source dest p q original addr F := by
  intro F
  obtain ⟨word,layout,placed⟩ := ready
  have off (i : Fin 35) (hi : i ≠ 34) : bank i ≠ next 34 := by
    rw [← fixed i hi]
    exact next.injective.ne hi
  obtain ⟨z,hz,run⟩ := dropWords_exec body (off 2 (by decide)) (bank.injective.ne (by decide : (2 : Fin 35) ≠ 0))
    (off 0 (by decide)).symm (d*d) H v S (by rw [layout.modulus,length_binSyms]) (layout.scratch 0 (by decide)).2
  have dropped : (S.R (next 34)).drop (d*d*H) = matrixWords A H older ++ rest := by
    rw [archive,List.append_assoc,← length_matrixWords A H newer,List.drop_left]
  rw [dropped] at run
  have keep (i : Fin 35) (hi : i ≠ 34) : F.R (next i) = S.R (bank i) := by
    simp [F,fixed i hi,off i hi]
  refine ⟨z,hz,run,word,?_,placed⟩
  constructor
  · exact (keep 2 (by decide)).trans layout.modulus
  · exact (keep 27 (by decide)).trans layout.width
  · exact (keep 28 (by decide)).trans layout.one
  · exact (keep 32 (by decide)).trans layout.padded
  · rw [keep 33 (by decide),layout.clock]
  · exact Function.update_self ..
  · intro i hi
    have ne : i ≠ 34 := fun e => (by decide : (34 : Fin 35) ∉ shearWork) (e ▸ hi)
    exact ⟨by simpa only [F,fixed i ne] using (layout.scratch i hi).1,(keep i ne).trans (layout.scratch i hi).2⟩
  · intro x
    rw [keep 24 (by decide),fixed 24 (by decide)]
    exact layout.src x
  · intro x
    rw [keep 25 (by decide),fixed 25 (by decide)]
    exact layout.dst x

end IntegerMultBounds.MathlibTM2.Cover.Fallback
