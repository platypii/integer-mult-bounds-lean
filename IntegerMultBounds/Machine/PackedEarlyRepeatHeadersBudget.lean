import IntegerMultBounds.Machine.PackedEarlyRepeatHeadersPlaced

/-! The shared early repetition-header lifecycle has a paid linear bound
in the actual reserved role volume, including erasure of both generated factors. -/
namespace IntegerMultBounds.Machine.PackedEarlyRepeatHeadersBudget
noncomputable section
open CompactGadgetReservationShape
open CompactGadgetReservationHeadersWords
open CompactGadgetReservationHeadersOps
open CompactGadgetReservationHeadersCost
open CompactGadgetReservationHeadersCarvedData (gap)
open PackedPrefixRepeatHeaders (initial construction values repetitions)
open PackedEarlyRepeatHeaders

theorem before_le (d G n q b gap V : ℕ) (hg : 0<gap)
    (hL : repetitions d G n q b gap≤V) : beforeSource d G n q≤V := by
  have hp : 0<2^(n*b) := by positivity
  exact ((Nat.le_mul_of_pos_right _ hp).trans (Nat.le_mul_of_pos_right _ hg)).trans hL

theorem within (hs : Fin 7 → List Bool) (d G n q b gap rows V : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values d G n q b gap rows i)
    (hcap : n*q≤d*G) (hgap : 0<gap)
    (hH : d*G≤V) (hL : repetitions d G n q b gap≤V) :
    WithinList schedule (initial hs) V := by
  have ht : 0<2^(d*G-n*q) := by positivity
  have hb : 0<2^(n*b) := by positivity
  have hp : 2^(d*G-n*q)*2^(n*b)≤V := (Nat.le_mul_of_pos_right _ hgap).trans hL
  have htail : 2^(d*G-n*q)≤V := (Nat.le_mul_of_pos_right _ hb).trans hp
  have hback : 2^(n*b)≤V := (Nat.le_mul_of_pos_left _ ht).trans hp
  have hnb : n*b≤V := (Nat.lt_pow_self (n := n*b) (by decide : 1<2)).le.trans hback
  have hnq : n*q≤V := hcap.trans hH
  have hdif : d*G-n*q≤V := (Nat.sub_le _ _).trans hH
  have hp' : 2^(n*b)*2^(d*G-n*q)≤V := by simpa only [Nat.mul_comm] using hp
  have hL' : gap*(2^(n*b)*2^(d*G-n*q))≤V := by
    simpa only [repetitions,Nat.mul_comm] using hL
  simp [schedule,construction,eraseSlots,WithinList,Within,transform,install,
    initial,Fin.addCases,value,word,hv,values,RecursiveChildQuotientsConstant.bits_value]
  exact ⟨hH,hnq,hH,htail,hnb,hback,hp',hL',hH,hnq,(by omega),hnb,hback,hp'⟩

theorem construction_bound (hs : Fin 7 → List Bool) (s : Shape) (n q b rows : ℕ)
    (hv : ∀ i,Counter.value (hs i)=values s.axes s.guard n q b (gap s (n*b) .control) rows i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hG : 0<s.guard) (hq : 0<q) (hb : 0<b) (hcapq : n*q≤s.H) (hcapb : n*b≤s.H)
    (hr : 0<rows) (hp : 0<s.payload) :
    bound schedule (initial hs)≤14*coefficient*(rows*s.recordWidth) := by
  have hg := PackedPrefixRepeatHeadersReserved.geometry_bounds s n q b rows hr hp hcapb
  have hV : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  have hl := list_bound schedule (initial hs) _ hV
    (ready hs s.axes s.guard n q b (gap s (n*b) .control) rows hv hc hG hq hb hcapq)
    (within hs s.axes s.guard n q b (gap s (n*b) .control) rows _ hv hcapq
      (CompactGadgetReservationHeadersCarvedData.gap_pos _ _ _) hg.1 hg.2)
  simpa only [schedule,construction,eraseSlots,List.length_append,List.length_map,
    List.length_cons,List.length_nil] using hl

theorem cleanup_bound (hs : Fin 7 → List Bool) (s : Shape) (n q b rows : ℕ)
    (hcapb : n*b≤s.H) (hr : 0<rows) (hp : 0<s.payload) :
    bound cleanup (finished hs s.axes s.guard n q b (gap s (n*b) .control))≤
      2*coefficient*(rows*s.recordWidth) := by
  have hL := (PackedPrefixRepeatHeadersReserved.geometry_bounds s n q b rows hr hp hcapb).2
  have hh := before_le s.axes s.guard n q b (gap s (n*b) .control) _
    (CompactGadgetReservationHeadersCarvedData.gap_pos _ _ _) hL
  have hV : 0<rows*s.recordWidth := by unfold Shape.recordWidth; positivity
  apply (list_bound cleanup _ _ hV _ _).trans_eq (by rfl)
  · simp [cleanup,ReadyList,Ready,Source,finished,word,transform,
      RecursiveChildQuotientsConstant.bits_canonical]
  · simp [cleanup,WithinList,Within,finished,value,word,transform,
      RecursiveChildQuotientsConstant.bits_value]
    exact ⟨hh,hL⟩

end
end IntegerMultBounds.Machine.PackedEarlyRepeatHeadersBudget
