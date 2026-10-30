module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloBatchProgram
public import IntegerMultBounds.MathlibTM2.Host.StackStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Persistent archive storage at a prefix of the actual numerical batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main

/-- Concrete stock lift beside the batch's isolated unary counter. -/
theorem packedHaloBatch_projected_stock_le {Q A : ℕ} {U : Type}
    (v : HS 249 Q A U) (S F : Stacks 249 A) (budget : ℕ)
    (hleft : F.L 248 = S.L 248) (hcount : (F.R 248).length ≤ (S.R 248).length)
    (hstock : mnSize (mk (embDn packedHaloBatchReg v) (embStk packedHaloBatchReg F)) ≤
      mnSize (mk (embDn packedHaloBatchReg v) (embStk packedHaloBatchReg S))+budget) :
    mnSize (mk v F) ≤ mnSize (mk v S)+budget := by
  apply projected_stock_le_shrinking_counter packedHaloBatchReg
    (fun i j he => Fin.ext (congrArg (fun k : Fin 249 => k.val) he)) v F S 248
    (fun i he => by have hv := congrArg Fin.val he; have hi := i.isLt; change i.val = 248 at hv; omega)
    budget ?_ hcount hstock
  intro j hj
  have hj248 : j = 248 := by
    have hge : 248 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 248 := by omega
      exact hj ⟨j.val,hlt⟩ (Fin.ext rfl)
    exact Fin.ext (by have := j.isLt; change j.val = 248; omega)
  subst j
  exact ⟨hleft,fun hn => False.elim (hn rfl)⟩

/-- The physical queue for an unprocessed suffix never exceeds the initial
queue. No fixed packet width or numerical property is needed for this fact. -/
theorem packedHaloQueue_length_le {A X : Type} (encode : X → List A)
    (done todo : List X) (tail initial current : List A)
    (hinit : initial = ((done++todo).map encode).flatten++tail)
    (hcurrent : current = (todo.map encode).flatten++tail) :
    current.length ≤ initial.length := by
  rw [hinit,hcurrent,List.map_append,List.flatten_append]
  simp only [List.length_append]
  omega

/-- Fixed-width packet queues are bounded by their remaining input count. -/
theorem packedHaloQueue_length {A X : Type} (encode : X → List A) (L : ℕ)
    (hencode : ∀ x, (encode x).length = L) (xs : List X) (tail : List A) :
    ((xs.map encode).flatten++tail).length = xs.length*L+tail.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.flatten_cons,List.length_append,List.length_cons,
      hencode,Nat.add_mul,Nat.one_mul] at *
    omega

theorem packedHaloQueue_length_le_of_count {A X : Type} (encode : X → List A) (L : ℕ)
    (hencode : ∀ x, (encode x).length = L) (xs todo : List X) (tail : List A)
    (hcount : todo.length ≤ xs.length) :
    ((todo.map encode).flatten++tail).length ≤ ((xs.map encode).flatten++tail).length := by
  rw [packedHaloQueue_length encode L hencode,packedHaloQueue_length encode L hencode]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right L hcount) _

theorem PackedHaloInputTrace.stock_le {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F)
    (v vf : HS 248 Q A U)
    (hframe : hostFrameStock F ≤ hostFrameStock S)
    (hother : ∀ i, i ≠ 132 → (F.R i).length ≤ (S.R i).length) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L := by
  apply mnSize_mk_le_archive v vf S F 132 (xs.length*L) hframe
  · have hlen := h.output_length hresult
    omega
  · exact hother

/-- The cursor allowance is retained once, independently of the prefix length. -/
theorem PackedHaloInputTrace.stock_le_cursor {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (h : PackedHaloInputTrace Result xs S F)
    (v vf : HS 248 Q A U) (V : ℕ)
    (hframe : hostFrameStock F ≤ hostFrameStock S)
    (hcursor : (F.R 157).length ≤ V)
    (hother : ∀ i, i ≠ 132 → i ≠ 157 → (F.R i).length ≤ (S.R i).length) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L+V := by
  have hb := mnSize_mk_le_allowance v vf S F
    (fun i => (if i = 132 then xs.length*L else 0)+(if i = 157 then V else 0)) hframe (by
      intro i
      by_cases ho : i = 132
      · subst i
        have hlen := h.output_length hresult
        simp only [ite_true,show (132 : Fin 248) ≠ 157 by decide,ite_false,Nat.add_zero]
        omega
      · by_cases hc : i = 157
        · subst i
          simp only [show (157 : Fin 248) ≠ 132 by decide,ite_false,ite_true,Nat.zero_add]
          omega
        · simpa [ho,hc] using hother i ho hc)
  simpa [Finset.sum_add_distrib,Nat.add_assoc] using hb

/-- Concrete between-input readiness discharges the register stock comparison.
The retained factor bank and spectator stacks are counted in the initial state. -/
theorem PackedHaloInputTrace.ready_stock_le_of_queue {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (htrace : PackedHaloInputTrace Result xs S F)
    {P stage q l s t u band a b V w W boundaryCount : ℕ}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (h' : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount F)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (h93 : F.R 93 = S.R 93)
    (haux : ∀ k : Fin 168, k ∈ haloAuxiliaryPorts →
      F.R (packedRecoveryRuntimeReg k) = S.R (packedRecoveryRuntimeReg k))
    (hhigh : ∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → F.R k = S.R k)
    (hqueue : (F.R 110).length ≤ (S.R 110).length)
    (v vf : HS 248 Q A U) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L+V := by
  apply htrace.stock_le_cursor hresult v vf V
    (hostFrameStock_congr hi ho hl).le h'.binaryLength
  intro k h132 h157
  by_cases h110 : k = 110
  · subst k; exact hqueue
  · exact (h.right_length_eq h' h93 haux hhigh k h110 h132 h157).le

theorem PackedHaloInputTrace.ready_stock_le {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (htrace : PackedHaloInputTrace Result xs S F)
    {P stage q l s t u band a b V w W boundaryCount : ℕ}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (h' : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount F)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (h93 : F.R 93 = S.R 93)
    (haux : ∀ k : Fin 168, k ∈ haloAuxiliaryPorts →
      F.R (packedRecoveryRuntimeReg k) = S.R (packedRecoveryRuntimeReg k))
    (hhigh : ∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → F.R k = S.R k)
    (encode : X → List (Fin (A+4))) (todo : List X) (tail : List (Fin (A+4)))
    (hsource : S.R 110 = ((xs++todo).map encode).flatten++tail)
    (hqueue : F.R 110 = (todo.map encode).flatten++tail)
    (v vf : HS 248 Q A U) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L+V := by
  apply htrace.ready_stock_le_of_queue hresult h h' hi ho hl h93 haux hhigh ?_ v vf
  exact packedHaloQueue_length_le encode xs todo tail _ _ hsource hqueue

theorem PackedHaloInputTrace.ready_stock_le_of_count {Q A : ℕ} {U X : Type}
    {Result : X → Stacks 248 A → Stacks 248 A → Prop} {L : ℕ}
    (hresult : ∀ x S F, Result x S F → (F.R 132).length = L+(S.R 132).length)
    {xs : List X} {S F : Stacks 248 A} (htrace : PackedHaloInputTrace Result xs S F)
    {P stage q l s t u band a b V w W boundaryCount : ℕ}
    (h : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount S)
    (h' : PackedHaloBetweenInputs P stage q l s t u band a b V w W boundaryCount F)
    (hi : F.inp = S.inp) (ho : F.out = S.out) (hl : F.L = S.L)
    (h93 : F.R 93 = S.R 93)
    (haux : ∀ k : Fin 168, k ∈ haloAuxiliaryPorts →
      F.R (packedRecoveryRuntimeReg k) = S.R (packedRecoveryRuntimeReg k))
    (hhigh : ∀ k : Fin 248, 168 ≤ k.val → k.val < 242 → F.R k = S.R k)
    (encode : X → List (Fin (A+4))) (packetLength : ℕ)
    (hencode : ∀ x, (encode x).length = packetLength) (initial todo : List X)
    (hcount : todo.length ≤ initial.length) (tail : List (Fin (A+4)))
    (hsource : S.R 110 = (initial.map encode).flatten++tail)
    (hqueue : F.R 110 = (todo.map encode).flatten++tail)
    (v vf : HS 248 Q A U) :
    mnSize (mk vf F) ≤ mnSize (mk v S)+xs.length*L+V := by
  apply htrace.ready_stock_le_of_queue hresult h h' hi ho hl h93 haux hhigh ?_ v vf
  rw [hsource,hqueue]
  exact packedHaloQueue_length_le_of_count encode packetLength hencode initial todo tail hcount

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
