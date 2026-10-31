module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseGatherArchive
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArchiveTileSource
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Physically pad and transpose an owned gathered archive. The returned
supplier-batch certificates describe the same actual bounded machine trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
namespace ArchiveTilePlan
variable {t₀ T Q c d W K s : ℕ}

theorem pad_route_gather_exec_within {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K) (hW : 0 < W)
    (rowSymbols padSymbols acc saved tmp replicas savedReplicas : Fin T)
    (hreg : [rowSymbols,padSymbols,plan.src,acc,saved,tmp,replicas,savedReplicas].Nodup)
    (width radius L w : ℕ) (hpacket : W = L*w)
    (hcapacity : (coreGatherIndices s width radius L).length ≤ (2^d)^c)
    (Fs : List (ZMod s → GaussianInt)) (hreplicas : Fs.length = 2^d)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.BankReady S)
    (hrow : (S.R rowSymbols).length = (coreGatherIndices s width radius L).length*L*w)
    (hpad : (S.R padSymbols).length = ((2^d)^c-(coreGatherIndices s width radius L).length)*L*w)
    (hsrc : S.R plan.src = cstream (prime+K) w (coreGatherPayload width radius L Fs))
    (hacc : S.R acc = []) (hcount : (S.R replicas).length = Fs.length)
    (hsavedReplicas : S.R savedReplicas = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ rows : Fin ((2^d)^c) → Fin (2^d) → List GaussianInt,
      (∀ i j, (rows i j).length = L) ∧
      (∀ i : Fin (coreGatherIndices s width radius L).length,
        (List.ofFn fun j => cstream (prime+K) w (rows (paddedCoreIndex hcapacity i) j)).flatten =
          cstream (prime+K) w (Fs.map (packedInterval
            (coreStart width (coreGatherIndices s width radius L)[i.val]-radius) L)).flatten) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ Fs.length*(6*((2^d)^c*L*w)+13)+6+plan.inverseCost S ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
          ((Fs.length*(((2^d)^c-(coreGatherIndices s width radius L).length)*L*w)+
            2*(4*((2^d)^c*L*w)+10))+plan.inverseStockAllowance)) depth
          (.seq (prefixPadRows rowSymbols padSymbols plan.src acc saved tmp replicas savedReplicas
            (pairSym (prime+K) false false)) plan.inverseProgram) (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
            ((List.ofFn fun i => (List.ofFn fun j => cstream (prime+K) w (rows i j)).flatten).flatten))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := padCoreGatherPayload_exec_within (body := body)
    rowSymbols padSymbols plan.src acc saved tmp replicas savedReplicas hreg ((2^d)^c) width radius L w
    hcapacity Fs [] v S hrow hpad (by simpa using hsrc) hacc hcount hsavedReplicas hsaved htmp depth
  let M : Stacks T (prime+K) := {S with R := (Function.update S.R plan.src
    (cstream (prime+K) w (paddedCoreGatherPayload ((2^d)^c) width radius L Fs)))}
  simp only [List.append_nil] at he₁
  obtain ⟨rows,hlen,hbatches,v₂,n₂,hu₂,hn₂,he₂⟩ := plan.inverse_gather_exec_within body hA hW
    width radius L w hpacket hcapacity Fs hreplicas v₁ M (hready.source_update _) (by simp [M]) depth
  have hvolume : (∑ j, (M.R (plan.ι j)).length) = ∑ j, (S.R (plan.ι j)).length := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [M,Function.update_of_ne (plan.hsourceOff j)]
  have hcost : plan.inverseCost M = plan.inverseCost S := by
    unfold inverseCost
    rw [hvolume]
  rw [hcost] at hn₂
  refine ⟨rows,hlen,hbatches,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  have hwhole := mn_seq_within_add he₁ he₂
  simpa only [M,Function.update_idem] using hwhole

end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
