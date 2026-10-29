module

public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! # Shared descriptor enumeration proof

Descriptor rows use index 4, count 15, and scratch 8–11. This structural loop
lemma shares emission ordering, framing, and instruction accounting between
core, halo, and movement-control generators.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem descriptorEnumeration_do {A W w N K : ℕ} (row : TblCode 16)
    (F : ℕ → List (Fin (A+4))) (st : TblSt 16 A)
    (hcount : st.val 15 = N) (hN : N < 2^W)
    (hrow : ∀ j < N, ∀ st₁ : TblSt 16 A,
      (∀ i, i ∉ [(4 : Fin 16),8,9,10,11] → st₁.val i = st.val i) → st₁.val 4 = j →
      TblDo A W w row st₁ (fun st₂ => st₂.acc = (F j).reverse++st₁.acc ∧
        ∀ i, i ∉ [(8 : Fin 16),9,10,11] → st₂.val i = st₁.val i) K) :
    TblDo A W w (tblFor 4 15 row) st
      (fun st' => st'.acc = ((List.range N).flatMap F).reverse++st.acc) (N*(K+3)+3) := by
  let Inv := fun j (st' : TblSt 16 A) =>
    (∀ i, i ∉ [(4 : Fin 16),8,9,10,11] → st'.val i = st.val i) ∧
      st'.acc = ((List.range j).flatMap F).reverse++st.acc
  have h : TblDo A W w (tblFor 4 15 row) st
      (fun st' => st'.acc = ((List.range N).flatMap F).reverse++st.acc)
      (1+(N*(K+1+2)+2)) := by
    apply TblDo.for N K hcount hN (by decide) Inv
    · constructor
      · intro i hi
        have hn : i ≠ (4 : Fin 16) := by intro he; apply hi; simp [he]
        simp [hn]
      · simp
    · intro j hj st₁ ⟨hf,hacc⟩ hindex hn
      exact (hrow j hj st₁ hf hindex).mono (fun st₂ ⟨hout,hframe⟩ =>
        ⟨(hframe 4 (by simp)).trans hindex,(hframe 15 (by simp)).trans hn,by
          constructor
          · intro i hi
            have h4 : i ≠ (4 : Fin 16) := by intro he; apply hi; simp [he]
            have hrest : i ∉ [(8 : Fin 16),9,10,11] := fun hm => hi (List.mem_cons_of_mem _ hm)
            simpa [h4] using (hframe i hrest).trans (hf i hi)
          · rw [hout,hacc,List.range_succ]
            simp [List.reverse_append,List.append_assoc]⟩) le_rfl
    · intro st' hI _ _
      exact hI.2
  exact h.mono (fun _ he => he) (by simp [Nat.add_assoc]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
