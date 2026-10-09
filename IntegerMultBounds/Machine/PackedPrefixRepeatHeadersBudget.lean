import IntegerMultBounds.Machine.PackedPrefixRepeatHeadersPlaced
import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCost

/-! Charge the complete physical prefix-factor construction and erasure
against a containing array volume. Intermediate powers and products are
bounded by the actual final repetition factor, rather than free descriptors. -/
namespace IntegerMultBounds.Machine.PackedPrefixRepeatHeadersBudget
noncomputable section
open PackedPrefixRepeatHeaders
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersOps
open CompactGadgetReservationHeadersCost

theorem within (hs : Fin 7 → List Bool) (d G n q b gap rows V : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hcap : n*q≤d*G) (hgap : 0<gap)
    (hH : d*G≤V) (hL : repetitions d G n q b gap≤V) :
    WithinList schedule (initial hs) V := by
  have ht : 0<2^(d*G-n*q) := by positivity
  have hb : 0<2^(n*b) := by positivity
  have hp : 2^(d*G-n*q)*2^(n*b)≤V :=
    (Nat.le_mul_of_pos_right _ hgap).trans hL
  have htail : 2^(d*G-n*q)≤V := (Nat.le_mul_of_pos_right _ hb).trans hp
  have hback : 2^(n*b)≤V := (Nat.le_mul_of_pos_left _ ht).trans hp
  have hnb : n*b≤V := (Nat.lt_pow_self (n := n*b) (by decide : 1<2)).le.trans hback
  have hnq : n*q≤V := hcap.trans hH
  have hdif : d*G-n*q≤V := (Nat.sub_le _ _).trans hH
  simp [schedule,construction,eraseSlots,WithinList,Within,transform,install,
    initial,Fin.addCases,value,word,hv,values,
    RecursiveChildQuotientsConstant.bits_value]
  have hp' : 2^(n*b)*2^(d*G-n*q)≤V := by simpa only [Nat.mul_comm] using hp
  have hL' : gap*(2^(n*b)*2^(d*G-n*q))≤V := by
    simpa only [repetitions,Nat.mul_comm] using hL
  exact ⟨hH,hnq,hH,htail,hnb,hback,hp',hL',hH,hnq,
    (by omega),htail,hnb,hback,hp'⟩

theorem construction_bound (hs : Fin 7 → List Bool) (d G n q b gap rows V : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<G) (hq : 0<q) (hb : 0<b) (hcap : n*q≤d*G)
    (hgap : 0<gap) (hV : 0<V)
    (hH : d*G≤V) (hL : repetitions d G n q b gap≤V) :
    bound schedule (initial hs)≤15*coefficient*V := by
  have h := list_bound schedule (initial hs) V hV
    (ready hs d G n q b gap rows hv hc hG hq hb hcap)
    (within hs d G n q b gap rows V hv hcap hgap hH hL)
  simpa only [schedule,construction,eraseSlots,List.length_append,List.length_map,
    List.length_cons,List.length_nil] using h

theorem cleanup_bound (d G n q b gap V : ℕ) (hV : 0<V)
    (hL : repetitions d G n q b gap≤V) :
    2*(RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap)).length+4≤8*V := by
  have hl := length_bound (RecursiveChildQuotientsConstant.bits (repetitions d G n q b gap))
    (RecursiveChildQuotientsConstant.bits_canonical _) V
    ((RecursiveChildQuotientsConstant.bits_value _).le.trans hL) hV
  omega

end
end IntegerMultBounds.Machine.PackedPrefixRepeatHeadersBudget
