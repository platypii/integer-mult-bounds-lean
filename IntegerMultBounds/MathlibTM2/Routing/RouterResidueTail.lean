module

public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry
public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Compute the residue-dependent terminal length from the common tail and
binary residue. All source and scratch words restore; only terminal output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

theorem routerResidueTail_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (L n K G r : ℕ)
    (hn : n < 2 ^ L) (hKn : K ≤ n) (hr : r < K)
    (v : HS T Q A U) (S : Stacks T A)
    (htail : S.R (rg 0) = binSyms L (routerTail n K G))
    (hresidue : S.R (rg 1) = binSyms L r)
    (hblank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → j ≠ 6 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (bsub (rg 0) (rg 1) (rg 2) (rg 3) (rg 4) (rg 5) (rg 6)) (mk v S) (8 * L + 8)
        (mk v' { S with R := (Function.update S.R (rg 2)
          (binSyms L (routerProfileParameters n K G r).m)) }) := by
  have ht : routerTail n K G ≤ n := by
    exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  have hrTail : r ≤ routerTail n K G := by
    rw [routerTail_eq n K G hKn]
    omega
  obtain ⟨v', hu, _, _, he⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 2) (tx := rg 3) (ty := rg 4) (tz := rg 5) (cy := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (ht.trans_lt hn) ((Nat.le_of_lt hr).trans hKn |>.trans_lt hn) v S htail hresidue
    (hblank 3 (by decide) (by decide) (by decide))
    (hblank 4 (by decide) (by decide) (by decide)) (hblank 5 (by decide) (by decide) (by decide))
  have hsub : (routerTail n K G + 2 ^ L - r) % 2 ^ L = routerTail n K G - r := by
    rw [show routerTail n K G + 2 ^ L - r = (routerTail n K G - r) + 2 ^ L by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt (ht.trans_lt hn))]
  rw [hsub, hblank 2 (by decide) (by decide) (by decide), List.append_nil] at he
  exact ⟨v', hu, he⟩

end IntegerMultBounds.MathlibTM2.Routing
