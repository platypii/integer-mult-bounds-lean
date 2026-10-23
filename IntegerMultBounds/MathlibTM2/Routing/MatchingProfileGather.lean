module

public import IntegerMultBounds.MathlibTM2.Routing.ResidueEntryOrder
public import IntegerMultBounds.MathlibTM2.Routing.MatchingProfileGenerate

/-! Common-table gathering produces exactly the endpoint order consumed by a
matching profile, for every residue satisfying the router geometry. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section
variable {T Q A : ℕ} {P U : Type}

def matchingMateCoordinate {N : ℕ} (mate : Fin N → Fin N) (q : ℕ) : ℕ :=
  if h : q < N then (mate ⟨q, h⟩).val else q

theorem matchingProfileEntries_gather (p : Par) (hK : 0 < p.K) (hρ : p.ρ < p.K)
    (mate : Fin p.wy → Fin p.wy) :
    (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate)).filter
        (fun x => decide (x.1 % p.K = p.ρ)) = matchingProfileEntries p hK mate := by
  rw [matchingTableEntries_filter_residue p.n p.K hK ⟨p.ρ, hρ⟩]
  unfold matchingProfileEntries
  apply congrArg List.ofFn
  funext c
  have hq := (profileTarget p hK c).isLt
  change p.ρ + c.val * p.K < p.wy at hq
  simp only [matchingMateCoordinate, dite_eq_left hq]
  rfl

theorem matchingProfileGather_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (out : Fin T) (hout : ∀ j, out ≠ rg j)
    (p : Par) (hK : 0 < p.K) (hρ : p.ρ < p.K) (mate : Fin p.wy → Fin p.wy)
    (L Lk : ℕ) (hwidth : p.wy < 2 ^ L) (hk : p.K < 2 ^ Lk)
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : S.R (rg 14) = matchingEntryWords L (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate)))
    (hblank : ∀ j : Fin 18, j = 0 ∨ j = 12 ∨ j = 13 ∨ (2 ≤ j.val ∧ j.val < 10) → S.R (rg j) = [])
    (hstride : S.R (rg 1) = binSyms Lk p.K) (hresidue : S.R (rg 11) = binSyms Lk p.ρ)
    (htmp : S.R (rg 16) = []) (hsaved : S.R (rg 15) = []) (haccum : S.R (rg 17) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ (p.n * p.K) * (residueDispatchCost L Lk + 28 * L + 47) +
        4 * ((p.n * p.K) * (2 * L + 2)) + 6 ∧
      Exec body (residueEntryGenerateProgram rg out) (mk v S) steps
        (mk v' { S with R := Function.update S.R out (matchingEntryWords L (matchingProfileEntries p hK mate) ++ S.R out) }) := by
  have hfit : ∀ x ∈ matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate), x.1 < 2 ^ L := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    have hq' := List.mem_range.mp hq
    have hw : p.n * p.K ≤ p.wy := by unfold Par.wy; omega
    exact (hq'.trans_le hw).trans hwidth
  have hr : p.ρ < 2 ^ Lk := hρ.trans hk
  obtain ⟨v', steps, hu, hm, he⟩ := residueEntryGenerate_exec body rg hrg out hout L Lk p.K p.ρ
    hk hK hr (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate)) hfit
    v S hinput hblank hstride hresidue htmp hsaved haccum
  have houtEq : residueEntryOutput (A := A) L p.K p.ρ
      (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate)) =
      matchingEntryWords L (matchingProfileEntries p hK mate) := by
    rw [residueEntryOutput, matchingProfileEntries_gather p hK hρ mate]
  rw [houtEq] at he
  have hlength : (matchingTableEntries (p.n * p.K) (matchingMateCoordinate mate)).length = p.n * p.K := by
    simp [matchingTableEntries]
  rw [hlength] at hm
  exact ⟨v', steps, hu, by omega, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
