module

public import IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldLayout
public import IntegerMultBounds.MathlibTM2.Routing.FieldOrderRun

/-! Physical field movement in the actual lexicographic tensor stream. Prefix,
spectator and fixed-width suffix records are derived from the enumeration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main CoordinateFieldLayout
variable {ι : Type} [DecidableEq ι]
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

theorem forward_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (width : ι → ℕ) (before middle suffix : List ι) (i : ι) (hi : i ∉ middle)
    (base : ι → ℕ) (R k : ℕ) (payload : (ι → ℕ) → List (Fin (A+4)))
    (hlen : ∀ coords, (payload coords).length = R)
    (hP : 0 < (before.map width).prod) (hB : 0 < (middle.map width).prod)
    (hW : 0 < (suffix.map width).prod*R) (hfit : width i ≤ 2^k) (zero : Fin (A+4))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hh : FieldOrderRun.Headers r k (before.map width).prod (middle.map width).prod
      (width i) ((suffix.map width).prod*R) S)
    (hf : ∀ j ∈ FieldOrderRun.scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = stream width (before++middle++i::suffix) base payload++tail) :
    let V := (before.map width).prod*((middle.map width).prod*(2^k*((suffix.map width).prod*R)))
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(60*V+3)+384*V+2 ∧
      Exec body (FieldOrderRun.forward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (stream width (before++i::(middle++suffix)) base payload++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (FieldOrderRun.forward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (stream width (before++i::(middle++suffix)) base payload++tail))})) := by
  let fill : Block (Fin (A+4)) ((suffix.map width).prod*R) :=
    ⟨List.replicate ((suffix.map width).prod*R) zero,by simp⟩
  obtain ⟨vf,n,hu,hn,he,hs⟩ := FieldOrderRun.forward_exec (body := body) r hr Subtype.val
    ((suffix.map width).prod*R) (before.map width).prod (middle.map width).prod (width i) k
    hW hP hB (fun x => x.property) fill zero rfl hfit (data width before middle suffix i base R payload hlen)
    tail v S hh hf (by rw [←stream_grouped]; exact hsrc)
  rw [←stream_swapped width before middle suffix i hi base R payload hlen] at he hs
  exact ⟨vf,n,hu,hn,he,hs⟩

theorem backward_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (width : ι → ℕ) (before middle suffix : List ι) (i : ι) (hi : i ∉ middle)
    (base : ι → ℕ) (R k : ℕ) (payload : (ι → ℕ) → List (Fin (A+4)))
    (hlen : ∀ coords, (payload coords).length = R)
    (hP : 0 < (before.map width).prod) (hB : 0 < (middle.map width).prod)
    (hW : 0 < (suffix.map width).prod*R) (hfit : width i ≤ 2^k) (zero : Fin (A+4))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hh : FieldOrderRun.Headers r k (before.map width).prod (middle.map width).prod
      (width i) ((suffix.map width).prod*R) S)
    (hf : ∀ j ∈ FieldOrderRun.scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = stream width (before++i::(middle++suffix)) base payload++tail) :
    let V := (before.map width).prod*((middle.map width).prod*(2^k*((suffix.map width).prod*R)))
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(64*V+3)+384*V+2 ∧
      Exec body (FieldOrderRun.backward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (stream width (before++middle++i::suffix) base payload++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (FieldOrderRun.backward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (stream width (before++middle++i::suffix) base payload++tail))})) := by
  let fill : Block (Fin (A+4)) ((suffix.map width).prod*R) :=
    ⟨List.replicate ((suffix.map width).prod*R) zero,by simp⟩
  obtain ⟨vf,n,hu,hn,he,hs⟩ := FieldOrderRun.backward_exec (body := body) r hr Subtype.val
    ((suffix.map width).prod*R) (before.map width).prod (middle.map width).prod (width i) k
    hW hP hB (fun x => x.property) fill zero rfl hfit
    (fun a t b => data width before middle suffix i base R payload hlen a b t)
    tail v S hh hf (by rw [←stream_swapped width before middle suffix i hi base R payload hlen]; exact hsrc)
  rw [←stream_grouped width before middle suffix i base R payload hlen] at he hs
  exact ⟨vf,n,hu,hn,he,hs⟩

end IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldRun
