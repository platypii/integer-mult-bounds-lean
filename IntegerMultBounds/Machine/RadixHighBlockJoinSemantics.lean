import IntegerMultBounds.Machine.RadixDigitMoveBlockRows

/-! Literal ordered high-block joining by successive single-radix movements.
The recursive arrays use the exact existing block-digit unmove operation. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinSemantics
noncomputable section
open RecursiveInterchangeRows (pack pack_val)
variable {a : ℕ}

def reindex {α : Type*} {n m : ℕ} (h : n=m) (x : Fin m → α) : Fin n → α :=
  fun z => x (Fin.cast h z)

private theorem input_succ (P S q r E : ℕ) :
    P*S*q*(q^r*E) = P*S*q^(r+1)*E := by rw [pow_succ]; ring
private theorem middle_succ (P S q r E : ℕ) :
    (P*q)*S*q^r*E = P*q*(S*(q^r*E)) := by ring
private theorem output_succ (P S q r E : ℕ) :
    P*q^(r+1)*(S*E) = (P*q)*q^r*(S*E) := by rw [pow_succ]; ring

/-- Take the leading radix digit after S, then continue with the extended
prefix. This order keeps the complete high-block digits in their original order. -/
def join (q : ℕ) : (r P S E : ℕ) →
    (Fin (P*S*q^r*E) → Fin (a+4)) → (Fin (P*q^r*(S*E)) → Fin (a+4))
  | 0,P,S,E,x => reindex (by simp; ring) x
  | r+1,P,S,E,x => reindex (output_succ P S q r E)
      (join q r (P*q) S E (reindex (middle_succ P S q r E)
        (RadixDigitMoveBlockRows.unmove (reindex (input_succ P S q r E) x))))

private theorem cast_pack {A B C D : ℕ} (h : A*B=C*D)
    (p : Fin A) (s : Fin B) (u : Fin C) (v : Fin D)
    (he : p.val*B+s.val = u.val*D+v.val) :
    Fin.cast h (pack p s) = pack u v := by
  apply Fin.ext
  simp only [Fin.val_cast,pack_val]
  exact he

/-- A literal joined cell is sourced from the original spectator/high order. -/
theorem join_entry (q r P S E : ℕ) (x : Fin (P*S*q^r*E) → Fin (a+4))
    (p : Fin P) (h : Fin (q^r)) (s : Fin S) (e : Fin E) :
    join q r P S E x (pack (pack p h) (pack s e)) = x (pack (pack (pack p s) h) e) := by
  induction r generalizing P p with
  | zero =>
    have hz : h.val = 0 := by simpa using h.isLt
    unfold join reindex
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast,pack_val,pow_zero]
    rw [hz]
    ring
  | succ r ih =>
    have heq : q^r*q = q*q^r := Nat.mul_comm _ _
    let hh : Fin (q*q^r) := Fin.cast (by rw [pow_succ]; exact heq) h
    obtain ⟨⟨j,t⟩,hht⟩ := finProdFinEquiv.surjective hh
    change pack j t = hh at hht
    have hv : h.val = j.val*q^r+t.val := by
      have hv := congrArg Fin.val hht
      simpa only [hh,Fin.val_cast,pack_val] using hv.symm
    unfold join
    change join q r (P*q) S E _ (Fin.cast (output_succ P S q r E) (pack (pack p h) (pack s e))) = _
    have ho : Fin.cast (output_succ P S q r E) (pack (pack p h) (pack s e)) =
        pack (pack (pack p j) t) (pack s e) := by
      apply Fin.ext
      simp only [Fin.val_cast,pack_val,pow_succ]
      rw [hv]
      ring
    rw [ho,ih]
    unfold reindex
    have hm : Fin.cast (middle_succ P S q r E) (pack (pack (pack (pack p j) s) t) e) =
        pack (pack p j) (pack s (pack t e)) := by
      apply Fin.ext
      simp only [Fin.val_cast,pack_val]
      ring
    rw [hm,RadixDigitMoveBlockRows.unmove_entry]
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast,pack_val,pow_succ]
    rw [hv]
    ring

/-- Successive paid single-digit moves implement exactly one whole-block
movement, without reversing or permuting the within-block digits. -/
theorem join_eq_unmove (q r P S E : ℕ) (x : Fin (P*S*q^r*E) → Fin (a+4)) :
    join q r P S E x = RadixDigitMoveBlockRows.unmove x := by
  funext z
  obtain ⟨⟨ph,se⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨p,h⟩,rfl⟩ := finProdFinEquiv.surjective ph
  obtain ⟨⟨s,e⟩,rfl⟩ := finProdFinEquiv.surjective se
  change join q r P S E x (pack (pack p h) (pack s e)) = _
  rw [join_entry]
  exact (RadixDigitMoveBlockRows.unmove_entry x p s h e).symm

end
end IntegerMultBounds.Machine.RadixHighBlockJoinSemantics
