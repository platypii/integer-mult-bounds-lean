import IntegerMultBounds.Machine.WordMoves

/-! Fixed control replacement of an equal-width word by a copied word.
The source remains intact, the destination exterior remains intact, and both
heads return to their origins, including for empty words. -/
namespace IntegerMultBounds.Machine.EqualWordReplace
variable {a : ℕ}

theorem overwrite (f : ℤ → Fin (a+4)) (p : ℤ) (xs ys : List (Fin (a+4)))
    (hlen : xs.length = ys.length) :
    putWord (putWord f p ys) p xs = putWord f p xs := by
  induction xs generalizing ys p with
  | nil => cases ys <;> simp_all [putWord]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [putWord]
      rw [putWord_update_before _ (p+1) p y xs (by omega), Function.update_idem,
        ih (p+1) ys (by simpa using hlen)]

def swap : Fin (1+1) ≃ Fin 2 where
  toFun := ![1,0]
  invFun := ![1,0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program (a : ℕ) : Program 2 7 a :=
  seq (seq CopyWord.program (extend ReturnOrigin.program 1))
    (reindex (extend ReturnOrigin.program 1) swap)

theorem first_bank (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    (ReturnOrigin.cfg f p 0).tapes.append (⟨fun _ => q,fun _ => g⟩ : Tapes 1 a) =
      (CopyWord.cfg f g p q).tapes := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem second_bank (f g : ℤ → Fin (a+4)) (p q : ℤ) :
    ((ReturnOrigin.cfg g q 0).tapes.append (⟨fun _ => p,fun _ => f⟩ : Tapes 1 a)).reindex swap =
      (CopyWord.cfg f g p q).tapes := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Copy and restore both heads with an exact linear bound, replacing all old cells. -/
theorem replace_hoare (f g : ℤ → Fin (a+4)) (p q : ℤ)
    (xs ys : List (Fin (a+4))) (hlen : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x ≠ blank) (hf : f (p-1) = blank)
    (hf' : f (p+xs.length) = blank) (hg : g (q-1) = blank) :
    HoareTime (program a)
      (fun v => v = (CopyWord.cfg (putWord f p xs) (putWord g q ys) p q).tapes)
      (fun v => v = (CopyWord.cfg (putWord f p xs) (putWord g q xs) p q).tapes)
      (3*xs.length+6) := by
  have h1 := CopyWord.copy_hoare f (putWord g q ys) p q xs hx hf'
  rw [overwrite g q xs ys hlen] at h1
  have h2 := hoare_extend_eq (ReturnOrigin.return_hoare_at f p xs hx hf)
    (⟨fun _ => q+xs.length,fun _ => putWord g q xs⟩ : Tapes 1 a)
  change HoareTime (extend ReturnOrigin.program 1)
    (fun v => v = (ReturnOrigin.cfg (putWord f p xs) (p+xs.length) 0).tapes.append _)
    (fun v => v = (ReturnOrigin.cfg (putWord f p xs) p 0).tapes.append _) _ at h2
  rw [first_bank,first_bank] at h2
  have h3 := hoare_place (ReturnOrigin.return_hoare_at g q xs hx hg) swap
    (⟨fun _ => p,fun _ => putWord f p xs⟩ : Tapes 1 a)
  change HoareTime (reindex (extend ReturnOrigin.program 1) swap)
    (fun v => v = ((ReturnOrigin.cfg (putWord g q xs) (q+xs.length) 0).tapes.append _).reindex swap)
    (fun v => v = ((ReturnOrigin.cfg (putWord g q xs) q 0).tapes.append _).reindex swap) _ at h3
  rw [second_bank,second_bank] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by omega)

end IntegerMultBounds.Machine.EqualWordReplace
