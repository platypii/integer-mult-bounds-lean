module

public import IntegerMultBounds.MathlibTM2.Routing.FieldOrderLayout
public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixRun
public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnColumns

/-! Physical changes of field order on explicitly indexed tensors. Both
orientations move only the polynomial-width local field; spectators are whole
records, and temporary padding is removed before returning. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FieldOrderRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main PaddedFieldLayout FieldOrderLayout
variable {T Q A : ℕ} {J U E : Type} {body : J → Pr J T Q A U}

structure Headers (r : Fin 16 → Fin T) (k P B M R : ℕ) (S : Stacks T A) : Prop where
  exponent : (S.R (r 0)).length = k
  prefixes : (S.R (r 1)).length = P
  spectator : (S.R (r 2)).length = B
  localLength : (S.R (r 3)).length = M
  recordWidth : (S.R (r 4)).length = R

def scratch : List (Fin 16) := [5,6,7,8,9,10,12,13,14,15]

def forward (r : Fin 16 → Fin T) (zero : Fin (A+4)) : Pr J T Q A U :=
  MixedRadixMove.moveField (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7)
    (r 8) (r 9) (r 10) (r 11) (r 12) (r 13) (r 14) (r 15) zero

def backward (r : Fin 16 → Fin T) (zero : Fin (A+4)) : Pr J T Q A U :=
  MixedRadixReturn.returnField (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7)
    (r 8) (r 9) (r 10) (r 11) (r 12) (r 13) (r 14) (r 15) zero

private theorem ports_nodup (r : Fin 16 → Fin T) (hr : Function.Injective r) :
    [r 0,r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,r 9,r 10,r 11,r 12,r 13,r 14,r 15].Nodup := by
  simp [List.nodup_cons,hr.eq_iff]

theorem forward_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (encode : E → List (Fin (A+4))) (R P B M k : ℕ) (hR : 0 < R) (hP : 0 < P) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : E) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero) (hfit : M ≤ 2^k)
    (f : ℕ → ℕ → ℕ → E) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hh : Headers r k P B M R S) (hf : ∀ j ∈ scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = stream encode P B M f++tail) :
    let V := P*(B*(2^k*R))
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(60*V+3)+384*V+2 ∧
      Exec body (forward r zero) (mk v S) n
        (mk vf {S with R := Function.update S.R (r 11) (stream encode P M B (fun a t b => f a b t)++tail)}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (forward r zero) (mk v S) n
        (mk vf {S with R := Function.update S.R (r 11) (stream encode P M B (fun a t b => f a b t)++tail)})) := by
  obtain ⟨vf,n,hu,hn,he,hs⟩ := MixedRadixRun.moveField_exec (body := body)
    (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12) (r 13) (r 14) (r 15)
    (ports_nodup r hr) encode R B M k hR hB hencode fill zero hfill (fibers P B M f)
    (by simpa only [fibers_length] using hP)
    (fun matrix hm => (fibers_shape P B M f matrix hm).1)
    (fun matrix hm => (fibers_shape P B M f matrix hm).2) hfit tail v S
    hh.exponent (by simpa only [fibers_length] using hh.prefixes) hh.spectator hh.localLength hh.recordWidth
    (by rw [sourceRows_stream]; exact hsrc) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hf _ (by simp [scratch]))
  refine ⟨vf,n,hu,?_,?_,?_⟩
  · simpa only [fibers_length] using hn
  · simpa only [forward,transposed_stream] using he
  · intro depth
    simpa only [forward,transposed_stream,fibers_length] using hs depth

theorem backward_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (encode : E → List (Fin (A+4))) (R P B M k : ℕ) (hR : 0 < R) (hP : 0 < P) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : E) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero) (hfit : M ≤ 2^k)
    (f : ℕ → ℕ → ℕ → E) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hh : Headers r k P B M R S) (hf : ∀ j ∈ scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = stream encode P M B f++tail) :
    let V := P*(B*(2^k*R))
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(64*V+3)+384*V+2 ∧
      Exec body (backward r zero) (mk v S) n
        (mk vf {S with R := Function.update S.R (r 11) (stream encode P B M (fun a b t => f a t b)++tail)}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (backward r zero) (mk v S) n
        (mk vf {S with R := Function.update S.R (r 11) (stream encode P B M (fun a b t => f a t b)++tail)})) := by
  obtain ⟨vf,n,hu,hn,he,hs⟩ := MixedRadixReturnColumns.returnColumns_exec (body := body)
    (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12) (r 13) (r 14) (r 15)
    (ports_nodup r hr) encode R B M k hR hB hencode fill zero hfill (fibers P M B f)
    (by simpa only [fibers_length] using hP)
    (fun matrix hm => (fibers_shape P M B f matrix hm).1)
    (fun matrix hm => (fibers_shape P M B f matrix hm).2) hfit tail v S
    hh.exponent (by simpa only [fibers_length] using hh.prefixes) hh.spectator hh.localLength hh.recordWidth
    hsrc (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hf _ (by simp [scratch]))
  refine ⟨vf,n,hu,?_,?_,?_⟩
  · simpa only [fibers_length] using hn
  · simpa only [backward,transposed_stream] using he
  · intro depth
    simpa only [backward,transposed_stream,fibers_length] using hs depth

end IntegerMultBounds.MathlibTM2.Routing.FieldOrderRun
