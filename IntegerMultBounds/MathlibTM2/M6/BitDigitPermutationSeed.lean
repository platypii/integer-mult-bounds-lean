module

public import IntegerMultBounds.MathlibTM2.M6.BitBasisWorkerSeed
public import IntegerMultBounds.MathlibTM2.M6.BitFlatChartRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- Initialize the actual permutation machine in a chart port. Every digit
swap borrows the same 35 spare tapes after the permutation bank. -/
theorem loadDigitPermutation {P U : Type} {T Q d spare : ℕ} (degree : 2 ≤ d) (room : 35 ≤ spare)
    (pairs : List {p : Fin d × Fin d // p.1 < p.2})
    (machine : {p : Fin d × Fin d // p.1 < p.2} → SharedBankSkeleton.Skeleton 1 prime)
    (K : ℕ) (fits : ∀ p, 1+(24+K) ≤ (machine p).tapes)
    (body : P → Pr P T Q prime U) (chart : Fin ((digitSwapSkeleton machine pairs).tapes+spare) ↪ Fin T)
    (source : Fin 4 → Fin T) (apart : ∀ k j, chart k ≠ source j) :
    let port := fun a => (digitSwapBank machine pairs a).trans ((Fin.castAddEmb spare).trans chart)
    let suffix := fun a (h : Fin (24+K)) => port a ((h.natAdd 1).castLE (fits pairs[a]))
    let tmp := ((Fin.castLEEmb room).trans (Fin.natAddEmb (digitSwapSkeleton machine pairs).tapes)).trans chart
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      S.R (source 0) = binSyms M.size M → S.R (source 1) = binSyms 1 1 →
      S.R (source 2) = binSyms W.size W → (S.R (source 3)).length = w →
      (∀ k, S.L (tmp k) = [] ∧ S.R (tmp k) = []) →
      (∀ a h, S.L (suffix a h) = [] ∧ S.R (suffix a h) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        (∀ a h, let p := pairs[a]
          let seed := swapPrivateStacks K (payloadView prime d (w+1) W) d p.val.1 p.val.2 (w+1)
          F.L (suffix a h) = seed.L h ∧ F.R (suffix a h) = seed.R h) ∧
        ∀ k, (∀ a h, suffix a h ≠ k) → F.L k = S.L k ∧ F.R k = S.R k := by
  intro port suffix tmp
  let inner (a : Fin pairs.length) := (Fin.natAddEmb 1 (m := 24+K)).trans (Fin.castLEEmb (fits pairs[a]))
  let dest a := (inner a).trans (port a)
  have external a h k : dest a h ≠ tmp k := chart.injective.ne (by
    intro eq
    have val := congrArg Fin.val eq
    change (digitSwapBank machine pairs a (inner a h)).val = (digitSwapSkeleton machine pairs).tapes+k.val at val
    have := (digitSwapBank machine pairs a (inner a h)).isLt
    omega)
  let bank a := appendPorts tmp (dest a) (fun k h => (external a h k).symm)
  have atData a h : bank a (h.natAdd 35) = suffix a h := by
    simp [bank,appendPorts,dest,inner,suffix]
  have sources a h k : bank a h ≠ source k := by
    induction h using Fin.addCases with
    | left h => simpa [bank,appendPorts,tmp] using apart ((h.castLE room).natAdd _) k
    | right h => rw [atData]; exact apart _ _
  obtain ⟨rate,code,run⟩ := loadSwapPortSchedule body (fun _ => K) bank source sources d degree
    (fun a => pairs[a].val.1) (fun a => pairs[a].val.2) (List.finRange pairs.length) (List.nodup_finRange _) (by
      intro a _ b _ ne h l
      change bank a (h.natAdd 35) ≠ bank b l
      rw [atData]
      induction l using Fin.addCases with
      | left l =>
        have eq : bank b (l.castAdd _) = tmp l := by simp [bank,appendPorts]
        rw [eq]; exact external a h l
      | right l =>
        rw [atData]
        exact ((Fin.castAddEmb spare).trans chart).injective.ne
          (digitSwapBank_disjoint machine pairs a b ne (inner a h) (inner b l)))
  refine ⟨rate,code,?_⟩
  intro w W pos u S M base unit width clock scratch vacant
  obtain ⟨z,F,n,exec,user,paid,loaded,off⟩ := run w W pos u S base unit width clock (by
    intro a _ k
    induction k using Fin.addCases with
    | left k => simpa [bank,appendPorts] using scratch k
    | right k => rw [atData]; exact vacant a k)
  refine ⟨z,F,n,exec,user,paid,?_,?_⟩
  · intro a h
    rw [← atData]
    exact loaded a (List.mem_finRange _) h
  · intro k away
    apply off
    intro a _ h
    change bank a (h.natAdd 35) ≠ k
    rw [atData]
    exact away a h

end IntegerMultBounds.MathlibTM2.M6.BitNode
