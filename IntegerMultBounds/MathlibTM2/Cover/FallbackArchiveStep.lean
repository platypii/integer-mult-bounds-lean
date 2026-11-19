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

/-- Consume the pivot and parent prefixes to expose the matrix and its reverse schedule. -/
theorem exposeReverseArchives_exec {r n : ℕ} (bank : Fin 35 ↪ Fin T) (stream : Fin T)
    (apart : ∀ i, bank i ≠ stream) (body : P → Pr P T Q A U) (v : HS T Q A U) (S : Stacks T A)
    (H J : ℕ) (pivot : Fin r → ZMod M) (parent : Fin n → ZMod M)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (tail code : List (Fin (A+4)))
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ)
    (original : Fin (M^d*W) → α) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let record := matrixWords A H matrix ++ tail
    let pack := fun {k : ℕ} (a : Fin k → ZMod M) => (List.ofFn fun j => binSyms (A := A) H (a j).val).flatten
    ColumnRecordReady bank H J (pack pivot ++ record) sym source dest p q original addr S →
    S.R stream = pack parent ++ code →
    let F := {S with R := Function.update (Function.update S.R (bank 34) record) stream code}
    ∃ z, z.user = v.user ∧ Exec body (.seq (dropWords (bank 2) (bank 34) (bank 0) r)
      (dropWords (bank 2) stream (bank 0) n)) (mk v S) ((r*(4*H+4)+1)+(n*(4*H+4)+1)) (mk z F) ∧
      ColumnReady bank H J matrix tail sym source dest p q original addr F := by
  intro record pack before schedule F
  obtain ⟨word,layout,placed⟩ := before
  have len {k} (a : Fin k → ZMod M) : (pack a).length = k*H := by
    simp [pack,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const]
  obtain ⟨u,hu,pop⟩ := dropWords_exec body (bank.injective.ne (by decide : (2 : Fin 35) ≠ 34))
    (bank.injective.ne (by decide : (2 : Fin 35) ≠ 0)) (bank.injective.ne (by decide : (34 : Fin 35) ≠ 0))
    r H v S (by rw [layout.modulus,length_binSyms]) (layout.scratch 0 (by decide)).2
  rw [layout.archive,← len pivot,List.drop_left] at pop
  let D := {S with R := Function.update S.R (bank 34) record}
  have keep (i : Fin 35) (hi : i ≠ 34) : D.R (bank i) = S.R (bank i) :=
    Function.update_of_ne (bank.injective.ne hi) _ _
  obtain ⟨z,hz,drop⟩ := dropWords_exec body (apart 2) (bank.injective.ne (by decide : (2 : Fin 35) ≠ 0))
    (apart 0).symm n H u D (by rw [keep 2 (by decide),layout.modulus,length_binSyms])
    ((keep 0 (by decide)).trans (layout.scratch 0 (by decide)).2)
  have queue : D.R stream = pack parent ++ code := (Function.update_of_ne (apart 34).symm _ _).trans schedule
  rw [queue,← len parent,List.drop_left] at drop
  have same (i : Fin 35) (hi : i ≠ 34) : F.R (bank i) = S.R (bank i) :=
    (Function.update_of_ne (apart i) _ _).trans (keep i hi)
  refine ⟨z,hz.trans hu,Exec.seq pop drop,word,?_,placed⟩
  constructor
  · exact (same 2 (by decide)).trans layout.modulus
  · exact (same 27 (by decide)).trans layout.width
  · exact (same 28 (by decide)).trans layout.one
  · exact (same 32 (by decide)).trans layout.padded
  · rw [same 33 (by decide),layout.clock]
  · exact (Function.update_of_ne (apart 34) _ _).trans (Function.update_self ..)
  · intro i hi
    exact ⟨(layout.scratch i hi).1,(same i (fun e => (by decide : (34 : Fin 35) ∉ shearWork) (e ▸ hi))).trans
      (layout.scratch i hi).2⟩
  · intro x; rw [same 24 (by decide)]; exact layout.src x
  · intro x; rw [same 25 (by decide)]; exact layout.dst x

end IntegerMultBounds.MathlibTM2.Cover.Fallback
