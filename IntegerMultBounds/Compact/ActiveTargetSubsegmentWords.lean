import IntegerMultBounds.Compact.ActiveTargetSubsegmentValue

/-! Literal selected-bit mask on a contiguous active target, with the omitted
highest operation separated onto the first bit of the retained high field. -/
namespace IntegerMultBounds.Compact.ActiveTargetSubsegmentWords
noncomputable section
open IntegerMultBounds.Counter (value)
open IntegerMultBounds.Machine
open PowerTwo

def ideal (q : ℕ) (lo V hi Z : List Bool) := lo++CountedIdealToggle.word q V Z++hi

theorem width (q rho : ℕ) (lo V hi Z : List Bool) (hq : 1≤q)
    (hlo : lo.length=rho) (hV : V.length=Z.length*q) (hhi : hi.length=q-rho) (hr : rho≤q) :
    (ideal q lo V hi Z).length=(Z.length+1)*q := by
  simp only [ideal,List.length_append,CountedIdealToggle.word_length q V Z hq hV,hlo,hV,hhi]
  rw [Nat.add_mul]
  omega

theorem spectators (q : ℕ) (lo V hi Z : List Bool) (hq : 1≤q) (hV : V.length=Z.length*q) :
    (ideal q lo V hi Z).take lo.length=lo ∧
    (ideal q lo V hi Z).drop (lo.length+V.length)=hi := by
  unfold ideal
  constructor
  · simp
  · rw [List.drop_append,List.drop_append]
    rw [List.drop_eq_nil_of_le (by omega : lo.length ≤ lo.length+V.length)]
    have hw := CountedIdealToggle.word_length q V Z hq hV
    rw [← hw]
    simp

theorem xor_zero (xs : List Bool) : List.zipWith xor xs (List.replicate xs.length false)=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.replicate_succ,ih]

/-- The full mask is zero on both spectator intervals and places each control
at the first bit of its q-bit active block. -/
theorem full_mask (q : ℕ) (lo V hi Z : List Bool) (hq : 1≤q) (hV : V.length=Z.length*q) :
    List.zipWith xor (lo++V++hi)
      (List.replicate lo.length false++toggleMask q Z++List.replicate hi.length false)=ideal q lo V hi Z := by
  rw [List.zipWith_append (by simp only [List.length_append,List.length_replicate,toggleMask_length q hq,hV]),
    List.zipWith_append (by simp only [List.length_replicate]),xor_zero,xor_zero]
  rfl

/-- The omitted highest selected operation changes only the first bit of hi. -/
def highest (z : Bool) : List Bool → List Bool
  | [] => []
  | a::hi => xor a z::hi

theorem highest_tail (z a : Bool) (hi : List Bool) : (highest z (a::hi)).tail=hi := rfl

theorem highest_value (z a : Bool) (hi : List Bool) :
    (value (highest z (a::hi)) : ℤ)=(value (a::hi) : ℤ)+PowerTwo.ctrl z*(1-2*PowerTwo.ctrl a) := by
  cases z <;> cases a <;> simp [highest,value,PowerTwo.ctrl]
  all_goals omega

/-- Low active toggles and the highest elementary toggle operate on disjoint
literal intervals; both retain every unselected containing-slot bit. -/
theorem highest_separate (q : ℕ) (lo V hi Z : List Bool) (z a : Bool) :
    ideal q lo V (highest z (a::hi)) Z=lo++CountedIdealToggle.word q V Z++(xor a z::hi) := rfl

theorem highest_xor (z a : Bool) (hi : List Bool) :
    List.zipWith xor (a::hi) (z::List.replicate hi.length false)=highest z (a::hi) := by
  simp only [List.zipWith_cons_cons,highest,xor_zero]

/-- All n+1 selected positions have now been supplied: rho low zeros, n
stride-q controls, then the highest control and the remaining high zeros. -/
theorem full_selected (q : ℕ) (lo V hi Z : List Bool) (z a : Bool)
    (hq : 1≤q) (hV : V.length=Z.length*q) :
    List.zipWith xor (lo++V++(a::hi))
      (List.replicate lo.length false++toggleMask q Z++(z::List.replicate hi.length false))=
      ideal q lo V (highest z (a::hi)) Z := by
  rw [List.zipWith_append (by simp only [List.length_append,List.length_replicate,toggleMask_length q hq,hV]),
    List.zipWith_append (by simp only [List.length_replicate]),xor_zero,highest_xor]
  rfl

theorem ideal_value (q rho : ℕ) (lo V hi Z : List Bool) (hq : 1≤q)
    (hlo : lo.length=rho) (hV : V.length=Z.length*q) :
    (value (ideal q lo V hi Z) : ℤ)=ActiveTargetSubsegmentValue.splice rho (Z.length*q)
      (value lo) (value (CountedIdealToggle.word q V Z)) (value hi) := by
  unfold ideal ActiveTargetSubsegmentValue.splice
  rw [ColumnTransducer.value_append,ColumnTransducer.value_append,List.length_append,
    CountedIdealToggle.word_length q V Z hq hV,hlo,hV,pow_add]
  push_cast
  ring

/-- Actual earlier kernel, reconstructed in its containing y slot, is the
literal XOR with zeros outside the active segment. Equality is guarded. -/
theorem early_good_word {S : Type*} (q b n rho : ℕ) (Z lo V hi : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hZ : Z.length=n) (hlo : lo.length=rho)
    (hV : V.length=Z.length*q)
    (x : BinaryPackedEarlyData.State q b n (ℤ×ℤ×S)) (ds : List DigitState)
    (hl : x.2.2.1=(value lo : ℤ)) (hh : x.2.2.2.1=(value hi : ℤ))
    (hc : ds.map DigitState.z=Z.map PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=Radix.pack ((2 : ℤ)^q) (ds.map DigitState.v))
    (hword : (value V : ℤ)=(x.1.val : ℤ))
    (hw : (x.2.1.val : ℤ)=Radix.pack ((2 : ℤ)^b) (ds.map DigitState.w))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    ActiveTargetSubsegmentValue.earlyTarget q b n rho (BinaryPackedEarlyData.run q b n Z hb hbq x)=
      (value (ideal q lo V hi Z) : ℤ) ∧ (BinaryPackedEarlyData.run q b n Z hb hbq x).2=x.2 := by
  have hq : 1≤q := by omega
  have h := ActiveTargetSubsegmentValue.early_good q b n rho Z hb hbq hZ x ds hc hv hw hg
  rw [ActiveTargetSubsegmentValue.early_toggle_word q b hq V Z ds hV hc (hword.trans hv) hg,hl,hh] at h
  have hi' := ideal_value q rho lo V hi Z hq hlo hV
  rw [hZ] at hi'
  rw [hi']
  exact h

/-- Both dirty compact fields and all y spectators are restored by the actual
later kernel; only the selected low-block parities change on good addresses. -/
theorem late_good_word {S : Type*} (q b n rho : ℕ) (X lo V hi : List Bool)
    (hb : 1≤b) (hbq : b+1≤q) (hX : X.length=n) (hlo : lo.length=rho)
    (hV : V.length=X.length*q)
    (x : BinaryPackedLateData.State q b n (ℤ×ℤ×S)) (ds : List LateDigitState)
    (hl : x.2.2.2.1=(value lo : ℤ)) (hh : x.2.2.2.2.1=(value hi : ℤ))
    (hc : ds.map LateDigitState.x=X.map PowerTwo.ctrl)
    (hv : (x.1.val : ℤ)=Radix.pack ((2 : ℤ)^q) (ds.map LateDigitState.v))
    (hword : (value V : ℤ)=(x.1.val : ℤ))
    (hw : (x.2.1.val : ℤ)=Radix.pack ((2 : ℤ)^b) (ds.map LateDigitState.w))
    (hu : (x.2.2.1.val : ℤ)=Radix.pack ((2 : ℤ)^b) (ds.map LateDigitState.u))
    (hg : ∀ d∈ds, d.Good ((2 : ℤ)^b) ((2 : ℤ)^(q-1))) :
    ActiveTargetSubsegmentValue.lateTarget q b n rho (BinaryPackedLateData.run q b n hb hbq X hX x)=
      (value (ideal q lo V hi X) : ℤ) ∧ (BinaryPackedLateData.run q b n hb hbq X hX x).2=x.2 := by
  have hq : 1≤q := by omega
  have h := ActiveTargetSubsegmentValue.late_good q b n rho hb hbq X hX x ds hc hv hw hu hg
  rw [ActiveTargetSubsegmentValue.late_toggle_word q b hq V X ds hV hc (hword.trans hv) hg,hl,hh] at h
  have hi' := ideal_value q rho lo V hi X hq hlo hV
  rw [hX] at hi'
  rw [hi']
  exact h

end
end IntegerMultBounds.Compact.ActiveTargetSubsegmentWords
