module

public import IntegerMultBounds.MathlibTM2.M6.BitRouteFactors

/-! A common denominator for both PR589 sweep charts. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks Certificates.PR589.Nine Matrix

theorem stageRoute_quarter (c : PortCertificate) (checked : c.Checked) (n : Fin 9) (a b : Axis) :
    ∃ z : ℤ, c.stageRoute n a b = (z : ℚ)/4 := by
  unfold PortCertificate.stageRoute
  split
  · rw [one_apply]
    split
    · exact ⟨4,by norm_num⟩
    · exact ⟨0,by norm_num⟩
  · rename_i h
    let s : Fin 8 := ⟨n.val-1,by omega⟩
    have spread (i x) : ∃ z : ℤ, c.spread s i x = (z : ℚ)/4 := by
      obtain ⟨z,_,_,eqn⟩ := c.spread_entry checked s i x
      exact ⟨2*z,by rw [eqn]; push_cast; ring⟩
    rcases a with i | x <;> rcases b with j | y
    · exact ⟨c.line i*c.line j,by rw [Int.cast_mul]; rfl⟩
    · exact spread i y
    · exact spread j x
    · change ∃ z : ℤ, avoid s x y = (z : ℚ)/4
      by_cases same : x = y
      · subst y
        by_cases active : x.1 = s
        · exact ⟨0,by simp [avoid,active]⟩
        · exact ⟨4,by simp [avoid,active]⟩
      · exact ⟨0,by simp [avoid,diagonal_apply_ne _ same]⟩

theorem fullChart_quarter (c : PortCertificate) (checked : c.Checked) (a : Axis) (b : ChartAxis) :
    ∃ z : ℤ, c.fullChart a b = (z : ℚ)/4 := by
  let q := c.fullChart a b
  have den := (fullChart_entry c checked a b).2
  change q.den ≤ 2 at den
  have pos := q.den_pos
  have eqn := Rat.num_div_den q
  change ∃ z : ℤ, q = (z : ℚ)/4
  rcases (show q.den = 1 ∨ q.den = 2 by omega) with h | h
  · exact ⟨4*q.num,by rw [h] at eqn; push_cast at eqn ⊢; linarith⟩
  · exact ⟨2*q.num,by rw [h] at eqn; push_cast at eqn ⊢; linarith⟩

/-- With the live inverse of four, a chart coefficient needs only its signed
integer numerator and a modular multiplication. -/
theorem ratMod_quarter {m : ℕ} {q : ℚ} (adm : q.den.Coprime m)
    (quarter : ∃ z : ℤ, q = (z : ℚ)/4) (inv : ZMod m) (inverse : inv*4 = 1) :
    IntegerMultBounds.Swap.Modular.ratMod m q = (((4*q).num : ℤ) : ZMod m)*inv := by
  obtain ⟨z,eqn⟩ := quarter
  have scaled : 4*q = (z : ℚ) := by rw [eqn]; ring
  rw [scaled,Rat.num_intCast]
  symm
  apply IntegerMultBounds.Swap.Modular.ratMod_unique m adm
  have h : (z : ℚ)*q.den = 4*q.num := by rw [← scaled,← Rat.mul_den_eq_num q]; ring
  have hz : z*(q.den : ℤ) = 4*q.num := by exact_mod_cast h
  have cast := congrArg (Int.cast : ℤ → ZMod m) hz
  push_cast at cast
  calc
    _ = ((z : ZMod m)*q.den)*inv := by ring
    _ = (q.num : ZMod m)*(inv*4) := by rw [cast]; ring
    _ = _ := by rw [inverse,mul_one]

end IntegerMultBounds.MathlibTM2.M6.BitNode
