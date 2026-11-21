module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryCall
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRun

/-! Pack an ordinary directory row on the same tapes used by the incoming transform. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open CrossWeightLayout HeadPivotLayout HeadWidthLayout GoodChildLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem ordinaryHeadPack_exec [M8.Machine.Net] {P U : Type} {T r g w W : ℕ}
    (bank : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ bank j) (body : P → Pr P T columnCapacity prime U)
    (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (weights : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ) (hW : 0 < W) :
    let M := prime^(w+1)
    let d := (r+g)+(r+g)
    let full := (Fin.castLEEmb (by decide : 58 ≤ 64)).trans bank
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let ordinary := ordinaryHead.trans (adapterBank.trans machine)
    let ports := columnPorts.trans (correctionColumnPlacement bank work apart)
    let is := ordinaryChildPackSchedule r g
    ∀ before : Fin (M^d*W) → ZMod 2,
    HeadColumnReady (d := d) (W := W) ((coeff false).trans ordinary) (shear.trans ordinary)
      M.size W.size [] weights [] SparseRoleCircuit.encode (fun _ => blank) dest 0 q before S →
    S.R (bank 44) = binSyms M.size (1 : ZMod M).val → (S.R (bank 45)).length = w →
    (∀ i, S.L (work (Fin.castSucc i)) = [] ∧ S.R (work (Fin.castSucc i)) = []) →
    ∃ u D n, u.user = v.user ∧
      n ≤ 1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1) ∧
      Exec body (statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d is))
        (mk v S) n (mk u D) ∧ RecordPayload (bank 24) (fun _ => blank) 0
          (before ∘ ordinaryRecursivePosition r g w W) D ∧
      (∀ k, 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []) ∧
      ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro M d full machine ordinary ports is before mid padded clock free
  have layout := correctionRecordEntry bank work apart M.size W.size d dest q S before
    mid.base mid.width mid.one padded clock (fun i _ => free _) (fun z => (mid.src z).symm)
    (fun z => (mid.dst z).symm)
  have clean (k : Fin (rowSwapBlock.tapes+35)) (hk : 35 ≤ k.val) :
      S.L (ports k) = [] ∧ S.R (ports k) = [] := by
    have off : ¬ ∃ j, columnBank (correctionColumnSlots j) = columnPorts k := by
      rintro ⟨j,h⟩
      have val := congrArg Fin.val h
      change (correctionColumnSlots j).val = k.val at val
      omega
    have eq : ports k = work (columnPorts k) := by
      change sharedRegisterPlacement work (correctionCallerSlots.trans bank) correctionRole (columnPorts k) = _
      unfold sharedRegisterPlacement
      rw [show correctionRole (columnPorts k) = none from dite_eq_right off]
    rw [eq]
    exact free k
  obtain ⟨u,D,n,user,time,run,_,payload,clear,frame⟩ := ordinaryIncomingPack_exec
    (r := r) (g := g) ports body v S _ dest q hW before layout clean
  refine ⟨u,D,n,user,time,run,?_,clear,frame⟩
  intro z
  rw [sub_zero]
  have read := payload z
  change readAt blank (D.L ((columnBank.trans (correctionColumnPlacement bank work apart)) 24))
    (D.R ((columnBank.trans (correctionColumnPlacement bank work apart)) 24)) z = _ at read
  rw [show (columnBank.trans (correctionColumnPlacement bank work apart)) 24 = bank 24 from
    correctionColumnPlacement_shared bank work apart 1] at read
  simpa only [swap_source_word,List.map_ofFn] using read

end IntegerMultBounds.MathlibTM2.M6.BitNode
