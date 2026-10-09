import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCost

/-! The setup schedule is linear in the complete concrete reserved role volume. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersVolume
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersData
open CompactGadgetReservationHeadersSchedule
open CompactGadgetReservationHeadersOps
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersCost

theorem within (hs : Fin 7 → List Bool) (s : Shape) (n rows : ℕ) (f : Front)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hr : 0 < rows) (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard)
    (hp : 0 < s.payload) (hn : n ≤ s.axes) :
    WithinList (schedule f) (initial hs) (rows*s.recordWidth) := by
  let V := rows*s.recordWidth
  have hH : 0 < s.H := Nat.mul_pos hd hG
  have hrec : 0 < s.recordWidth := by unfold Shape.recordWidth; positivity
  have hV : 0 < V := Nat.mul_pos hr hrec
  have hrecord : s.recordWidth ≤ V := by dsimp only [V]; nlinarith
  have hpow : 2^s.bits ≤ V := (Nat.le_mul_of_pos_right _ hp).trans hrecord
  have hbits : s.bits ≤ V := (Nat.lt_pow_self (n := s.bits) (by decide : 1 < 2)).le.trans hpow
  have hpower (k : ℕ) (hk : k ≤ s.bits) : 2^k ≤ V := (Nat.pow_le_pow_right (by decide) hk).trans hpow
  have hrf := roundFront_eq s hH hK
  have hrb := roundBack_eq s hH hK
  have hw := s.carved_le n hn
  have he := s.bits_decomposition n hn f
  have hrfbit : roundFront s ≤ s.bits := by unfold Shape.bits; omega
  have hrbbit : roundBack s ≤ s.bits := by unfold Shape.bits; omega
  have hHbit : s.H ≤ s.bits := by unfold Shape.bits; omega
  have hwbit : s.width n ≤ s.bits := hw.trans hHbit
  have hab : s.active*s.chunk ≤ s.bits := by unfold Shape.bits; omega
  have hprefix : rows*2^(s.prefixBits f) ≤ V := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s.prefixBits f ≤ s.bits)
    have hpw := Nat.le_mul_of_pos_right (2^s.bits) hp
    dsimp only [V]
    unfold Shape.recordWidth
    nlinarith
  have hgap : 2^(gapExponent s n f)*2^(s.active*s.chunk) ≤ V := by
    rw [← pow_add,gap_exponent s n hn f hH hK]
    exact hpower _ (by omega)
  have hsuf : 2^(suffixExponent s n)*s.payload ≤ V := by
    rw [suffix_exponent s n hn hH hK]
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : s.afterBits n ≤ s.bits)
    have h' : 2^(s.afterBits n)*s.payload ≤ s.recordWidth := Nat.mul_le_mul_right _ h
    exact h'.trans hrecord
  have hge : gapExponent s n f ≤ s.bits := by have h := gap_exponent s n hn f hH hK; omega
  have hse : suffixExponent s n ≤ s.bits := by rw [suffix_exponent s n hn hH hK]; omega
  have hprefixpow := hpower (s.prefixBits f) (by omega)
  have hgapPower := hpower (gapExponent s n f) hge
  have hsufPower := hpower (suffixExponent s n) hse
  have hactivePower := hpower (s.active*s.chunk) hab
  have hrfV := hrfbit.trans hbits
  have hrbV := hrbbit.trans hbits
  have hwV := hwbit.trans hbits
  have hHV := hHbit.trans hbits
  have haV := hab.trans hbits
  have h2H : 2*s.H ≤ V := by unfold Shape.bits at hbits; omega
  have hgeV := hge.trans hbits
  have hseV := hse.trans hbits
  cases f
  all_goals simp [schedule,construction,cleanup,eraseSlots,WithinList,Within,transform,install,
    initial,Fin.addCases,value,word,hv,originalValues,gapSource,prefixSource,
    RecursiveChildQuotientsConstant.bits_value,Nat.mul_comm]
  all_goals simp only [Shape.H,CompactGadgetReservationCapacity.capacity,Shape.width,
    Shape.prefixBits,gapExponent,suffixExponent,roundFront,roundBack,Nat.mul_comm,Nat.sub_sub] at *
  all_goals omega

theorem cost_bound (hs : Fin 7 → List Bool) (s : Shape) (n rows : ℕ) (f : Front)
    (hv : ∀ i, Counter.value (hs i) = originalValues s n rows i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (hr : 0 < rows) (hK : 0 < s.chunk) (hd : 0 < s.axes) (hG : 0 < s.guard)
    (hp : 0 < s.payload) (hn : n ≤ s.axes) :
    bound (schedule f) (initial hs) ≤ 32*coefficient*(rows*s.recordWidth) := by
  have hV : 0 < rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have h := list_bound (schedule f) (initial hs) _ hV (ready hs s n rows f hv hc hK hd hG hn)
    (within hs s n rows f hv hr hK hd hG hp hn)
  simpa only [schedule,construction,cleanup,eraseSlots,List.length_append,List.length_map,
    List.length_cons,List.length_nil] using h

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersVolume
