module

public import IntegerMultBounds.MathlibTM2.Host.ExchangePairStock

/-! Four disjoint, length-preserving prefix exchanges are two paired exchanges. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_exchange_four_size (r : Fin 8 → Fin T) (hr : Function.Injective r)
    (v w : HS T Q A U) (S : Stacks T A)
    (xs us tails : Fin 4 → List (Fin (A+4)))
    (hsource : ∀ i : Fin 4, S.R (r ⟨i.val,by omega⟩) = xs i++tails i)
    (hlen : ∀ i, (us i).length = (xs i).length) :
    let F : Stacks T A := {S with R := (Function.update (Function.update (Function.update
      (Function.update S.R (r 0) (tails 0)) (r 1) (tails 1))
      (r 4) (us 0++S.R (r 4))) (r 5) (us 1++S.R (r 5)))}
    mnSize (mk w {F with R := (Function.update (Function.update (Function.update
      (Function.update F.R (r 2) (tails 2)) (r 3) (tails 3))
      (r 6) (us 2++F.R (r 6))) (r 7) (us 3++F.R (r 7)))}) = mnSize (mk v S) := by
  dsimp only
  let F : Stacks T A := {S with R := (Function.update (Function.update (Function.update
    (Function.update S.R (r 0) (tails 0)) (r 1) (tails 1))
    (r 4) (us 0++S.R (r 4))) (r 5) (us 1++S.R (r 5)))}
  have h₁ := mn_exchange_pair_size (r 0) (r 1) (r 4) (r 5)
    ((show ([0,1,4,5] : List (Fin 8)).Nodup by decide).map hr)
    v v S (xs 0) (xs 1) (us 0) (us 1) (tails 0) (tails 1)
    (hsource 0) (hsource 1) (hlen 0) (hlen 1)
  have h₂ := mn_exchange_pair_size (r 2) (r 3) (r 6) (r 7)
    ((show ([2,3,6,7] : List (Fin 8)).Nodup by decide).map hr)
    v w F (xs 2) (xs 3) (us 2) (us 3) (tails 2) (tails 3)
    (by simpa [F,hr.eq_iff] using hsource 2)
    (by simpa [F,hr.eq_iff] using hsource 3) (hlen 2) (hlen 3)
  exact h₂.trans h₁

end IntegerMultBounds.MathlibTM2.Host
