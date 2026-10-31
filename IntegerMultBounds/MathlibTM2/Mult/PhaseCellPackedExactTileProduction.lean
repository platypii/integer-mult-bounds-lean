module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedExactTileSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTile
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreTileRows

/-! The actual packed producer feeds its computed rows into the conditional
archive transpose. Metadata readiness follows from the producer frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {t₀ T Q K s c d : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem packedExactTileProduction_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ (prime+K))
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result clock savedClock : Fin T)
    (hreg : [src,saved,count,tmp,spare,result,clock,savedClock].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result,clock,savedClock])
    (records : List (PackedNormalizedJob (prime+K) s)) (W : ℕ) (hwidth : ∀ r ∈ records, r.W = W) (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (t : ℕ) [NeZero t] (ht : ∀ r ∈ records, r.t = t)
    (hp : ∀ r ∈ records, 4 ≤ r.p) (htarget : ∀ r ∈ records, r.p+2 ≤ r.targetOut)
    (hlocal : ∀ r ∈ records, r.localityTarget = r.targetOut)
    (J : PackedNormalizedJob (prime+K) s → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : ∀ r ∈ records, J r ∘L IntegerMultBounds.NLogN.PhaseCellOperator.exact s t r.α = 1)
    (L : ℕ) (hreplicas : ∀ r ∈ records, r.Fs.length = 2^d)
    (hcore : ∀ r ∈ records, IntegerMultBounds.NLogN.PhaseCellMatrix.coreLength s r.coreWidth r.k = L)
    (plan : ArchiveTilePlan t₀ T Q c d (L*W)) (hplanSrc : plan.src = result)
    (hN : records.length ≤ (2^d)^c) (hvolume : 0 < records.length → 0 < L*W)
    (hbank : plan.BankReady S) (hresult : S.R result = [])
    (rest : List (Fin ((prime+K)+4)))
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ k ∈ [count,tmp,spare], S.R k = [])
    (hsource : S.R src = descriptorScheduleTape work PackedNormalizedJob.words records.reverse++rest)
    (hclock : (S.R clock).length = records.length) (hsaved : S.R saved = []) (hsavedClock : S.R savedClock = []) :
    let step := packedNormalizedDescriptorStep (P := P) (U := U) (A := prime+K) work src saved count tmp spare result hR hQ
    ∃ tileRows : Fin records.length → Fin (2^d) → List GaussianInt,
      (∀ i j, (tileRows i j).length = L) ∧
      (∀ i : Fin records.length, (records.get i).ExactRowOutput (J (records.get i)) (List.ofFn (tileRows i))) ∧
      ∃ tile : ArchiveTilePlan.Result L tileRows,
        tile.capacity = ArchiveTilePlan.capacity records.length ((2^d)^c) ∧
        ∃ v' n, v'.user = v.user ∧ n ≤ ((records.reverse.map (fun r => takeDescriptorBankCost (placedDescriptorFields work r.words)+
        r.setupTime+r.cleanup (U := U) hR hQ+3)).sum+
        (records.reverse.map (fun r => r.Fs.length*r.replicaTime)).sum+6*records.length+
        2*(descriptorScheduleTape work PackedNormalizedJob.words records.reverse).length+10)+plan.conditionalCost records.length S ∧
          Exec body (.seq (descriptorSolverSchedule src saved tmp clock savedClock step) (plan.conditionalProgram clock))
            (mk v S) n (mk v' {S with R := (Function.update S.R result
              ((List.ofFn fun j => cstream (prime+K) W (List.ofFn fun i => tile.padded i j).flatten).flatten))}) := by
  dsimp only
  obtain ⟨v₁,n₁,tileRows,hu₁,hn₁,he₁,hlen,hcert,hstock⟩ := packedExactTileSchedule_exec (body := body)
    hR hQ hA work hwork src saved count tmp spare result clock savedClock hreg hsep records W hwidth v S
    t ht hp htarget hlocal J hJ (2^d) L hreplicas hcore rest hblank hleft hscratch hsource hclock hsaved hsavedClock
  let raw := (List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) W (tileRows i j)).flatten).flatten
  let M : Stacks T (prime+K) := {S with R := Function.update S.R plan.src raw}
  have he₁' : Exec body (descriptorSolverSchedule src saved tmp clock savedClock
      (packedNormalizedDescriptorStep work src saved count tmp spare result hR hQ)) (mk v S) n₁ (mk v₁ M) := by
    simpa only [hresult,List.append_nil,M,hplanSrc] using he₁
  have hready : plan.Ready W tileRows M := hbank.ready_source W tileRows
  have hr := hreg
  regs_ne hr
  have hclockM : (M.R clock).length = records.length := by
    simp only [M,hplanSrc,Function.update_of_ne ‹result ≠ clock›.symm]
    exact hclock
  have hflag : (M.R clock).head?.isSome = decide (0 < records.length) := by
    have hh : (M.R clock).head?.isSome = decide (0 < (M.R clock).length) := by
      cases M.R clock <;> rfl
    simpa only [hclockM] using hh
  obtain ⟨tile,hcapacity,v₂,n₂,hu₂,hn₂,he₂⟩ := plan.conditional_exec clock body (by omega) hvolume L W rfl hN
    tileRows hlen v₁ M hready hflag
  have hbankR (j : Fin (swapT t₀)) : M.R (plan.ι j) = S.R (plan.ι j) := by
    simp [M,plan.hsourceOff j]
  have hcost : plan.conditionalCost records.length M = plan.conditionalCost records.length S := by
    simp only [ArchiveTilePlan.conditionalCost,ArchiveTilePlan.cost,hbankR]
  rw [hcost] at hn₂
  refine ⟨tileRows,hlen,hcert,tile,hcapacity,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  have hleftAll : (fun _ : Fin T => ([] : List (Fin (prime+K+4)))) = S.L := by
    funext i; exact (hbank.hL i).symm
  have he := Exec.seq he₁' he₂
  simpa only [M,hleftAll,hplanSrc,Function.update_idem] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
