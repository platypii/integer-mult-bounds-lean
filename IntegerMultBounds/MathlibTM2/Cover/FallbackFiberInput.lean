module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackOffset
public import IntegerMultBounds.Machine.TranslationExecutionReuse
public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

/-! Write the computed offset directly into the translation machine's descriptor slot. -/
public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host TranslationExecutionReuse
variable {T Q A : ℕ} {P U : Type}

private theorem fixedSlot (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4)))
    (bs ms offset : List Bool) (i : Fin 12) (hi : i ≠ 8) :
    (input source dest p q blocks bs ms offset).tape i =
      (input source dest p q blocks bs ms []).tape i ∧
    (input source dest p q blocks bs ms offset).head i =
      (input source dest p q blocks bs ms []).head i := by
  fin_cases i <;> first | exact ⟨rfl,rfl⟩ | contradiction

/-- A retained separator on the left of slot eight lets arithmetic write the
descriptor in place. Every other translation tape retains its represented contents. -/
theorem fiberInput_exec (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (call : Fin 12 ↪ Fin T) (slot : call 8 = r 3)
    (L c x M : ℕ) (hc : c < M) (hx : x < M) (hM : M < 2^L)
    (v : HS T Q A U) (S : Stacks T A) (hcoef : S.R (r 0) = binSyms L c)
    (hdigit : S.R (r 1) = binSyms L x) (hmod : S.R (r 2) = binSyms L M)
    (hblank : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = [])
    (marker : S.L (r 3) = [separator])
    (source dest : ℤ → Fin 4) (p q : ℤ) (blocks : List (List (Fin 4))) (bs ms : List Bool)
    (rep : RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
      (input source dest p q blocks bs ms [])) (S.L ∘ call) (S.R ∘ call)) :
    ∃ offset v' n, GrowingCounterData.Canonical offset ∧ Counter.value offset = c*x % M ∧
      v'.user = v.user ∧ n ≤ 48*L*L+154*L+70 ∧
      let F : Stacks T A := {S with R := Function.update S.R (r 3) (offset.map bitSymbol)}
      Exec body (offsetProgram r) (mk v S) n (mk v' F) ∧
      RepT (Alphabet.mapTapes RadixToBinary.binaryEncoding
        (input source dest p q blocks bs ms offset)) (F.L ∘ call) (F.R ∘ call) := by
  obtain ⟨offset,v',n,ho,hv,hu,hn,he⟩ :=
    offset_exec body r r.injective L c x M hc hx hM v S hcoef hdigit hmod hblank
  refine ⟨offset,v',n,ho,hv,hu,hn,he,?_⟩
  intro i z
  by_cases hi : i = 8
  · subst i
    change RadixZeroFill.encodedBinary offset z =
      readAt blank (S.L (call 8)) (Function.update S.R (r 3) _ (call 8)) (z-1)
    rw [slot,marker,Function.update_self,readAt_single,encodedBinary_eq]
  · obtain ⟨ht,hh⟩ := fixedSlot source dest p q blocks bs ms offset i hi
    have hne : call i ≠ r 3 := slot ▸ call.injective.ne hi
    simpa only [Alphabet.mapTapes,Function.comp_apply,ht,hh,Function.update_of_ne hne] using rep i z

end IntegerMultBounds.MathlibTM2.Cover.Fallback
