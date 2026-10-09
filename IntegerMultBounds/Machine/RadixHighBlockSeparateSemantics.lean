import IntegerMultBounds.Machine.RadixHighBlockJoinSemantics

/-! Literal inverse ordered high-block separation, moving the trailing
prefix digit after S at each step. -/
namespace IntegerMultBounds.Machine.RadixHighBlockSeparateSemantics
noncomputable section
open RecursiveInterchangeRows (pack pack_val)
variable {a : ℕ}
private theorem input_succ (P S q r E : ℕ) : (P*q^r)*q*(S*E) = P*q^(r+1)*(S*E) := by rw [pow_succ]; ring
private theorem middle_succ (P S q r E : ℕ) : P*q^r*(S*(q*E)) = (P*q^r)*S*q*E := by ring
private theorem output_succ (P S q r E : ℕ) : P*S*q^(r+1)*E = P*S*q^r*(q*E) := by rw [pow_succ]; ring

def separate (q : ℕ) : (r P S E : ℕ) →
    (Fin (P*q^r*(S*E)) → Fin (a+4)) → (Fin (P*S*q^r*E) → Fin (a+4))
  | 0,P,S,E,x => RadixHighBlockJoinSemantics.reindex (by simp; ring) x
  | r+1,P,S,E,x => RadixHighBlockJoinSemantics.reindex (output_succ P S q r E)
      (separate q r P S (q*E) (RadixHighBlockJoinSemantics.reindex (middle_succ P S q r E)
        (RadixDigitMoveBlockRows.move (RadixHighBlockJoinSemantics.reindex (input_succ P S q r E) x))))

theorem separate_entry (q r P S E : ℕ) (x : Fin (P*q^r*(S*E)) → Fin (a+4))
    (p : Fin P) (s : Fin S) (h : Fin (q^r)) (e : Fin E) :
    separate q r P S E x (pack (pack (pack p s) h) e) = x (pack (pack p h) (pack s e)) := by
  induction r generalizing E e with
  | zero =>
    have hz : h.val = 0 := by simpa using h.isLt
    unfold separate RadixHighBlockJoinSemantics.reindex
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast,pack_val,pow_zero]
    rw [hz]
    ring
  | succ r ih =>
    let hh : Fin (q^r*q) := Fin.cast (pow_succ q r) h
    obtain ⟨⟨t,j⟩,hht⟩ := finProdFinEquiv.surjective hh
    change pack t j = hh at hht
    have hv : h.val = t.val*q+j.val := by
      have hv := congrArg Fin.val hht
      simpa only [hh,Fin.val_cast,pack_val] using hv.symm
    unfold separate
    change separate q r P S (q*E) _ (Fin.cast (output_succ P S q r E) (pack (pack (pack p s) h) e)) = _
    have ho : Fin.cast (output_succ P S q r E) (pack (pack (pack p s) h) e) =
        pack (pack (pack p s) t) (pack j e) := by
      apply Fin.ext
      simp only [Fin.val_cast,pack_val,pow_succ]
      rw [hv]
      ring
    rw [ho,ih]
    unfold RadixHighBlockJoinSemantics.reindex
    have hm : Fin.cast (middle_succ P S q r E) (pack (pack p t) (pack s (pack j e))) =
        pack (pack (pack (pack p t) s) j) e := by
      apply Fin.ext
      simp only [Fin.val_cast,pack_val]
      ring
    rw [hm,RadixDigitMoveBlockRows.move_entry]
    congr 1
    apply Fin.ext
    simp only [Fin.val_cast,pack_val,pow_succ]
    rw [hv]
    ring

theorem separate_eq_move (q r P S E : ℕ) (x : Fin (P*q^r*(S*E)) → Fin (a+4)) :
    separate q r P S E x = RadixDigitMoveBlockRows.move x := by
  funext z
  obtain ⟨⟨psh,e⟩,rfl⟩ := finProdFinEquiv.surjective z
  obtain ⟨⟨ps,h⟩,rfl⟩ := finProdFinEquiv.surjective psh
  obtain ⟨⟨p,s⟩,rfl⟩ := finProdFinEquiv.surjective ps
  change separate q r P S E x (pack (pack (pack p s) h) e) = _
  rw [separate_entry]
  exact (RadixDigitMoveBlockRows.move_entry x p s h e).symm

end
end IntegerMultBounds.Machine.RadixHighBlockSeparateSemantics
