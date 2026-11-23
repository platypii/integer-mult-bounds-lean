module

public import IntegerMultBounds.MathlibTM2.M6.BitMixedIdleCost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem transposeRead {child wide interval : Descriptor} {m : ℕ}
    (position : Fin (volume prime child) ≃ Fin m) (size : volume prime wide = m)
    (same : wide = interval) (span : volume prime interval = m)
    (coords : InheritedIntervalPositions child interval span position) (width : wide.width = child.width)
    (x : Fin (volume prime wide) → ZMod 2) :
    ∀ k, Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x ((position k).cast size.symm) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun j => x ((position j).cast size.symm)) k := by
  subst interval
  exact (coords.transpose_iff width (fun k => x (k.cast size.symm))
    (fun k => Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x (k.cast size.symm))).2
    (by simp only [Fin.cast_cast,Fin.cast_eq_self])

private theorem copyIntervalRead {child : Descriptor} {w W : ℕ}
    (width : child.width = 7*w)
    (position : Fin (volume prime child) ≃ Fin ((prime^w)^16*(W*142080)))
    (coords : CopyIntervalPositions child w (W*142080) position) :
    let lane := phaseIntervalChild 0 7 w W
    let wide := {lane with afterD := lane.afterD*142080}
    ∀ (size : volume prime wide = (prime^w)^16*(W*142080)) (x : Fin (volume prime wide) → ZMod 2) k,
      Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x ((position k).cast size.symm) =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun j => x ((position j).cast size.symm)) k := by
  intro lane wide size x
  have shape : wide = phaseIntervalChild 0 7 w (W*142080) := by
    simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
  exact transposeRead position size shape _ coords (by simpa only [wide,lane,phaseIntervalChild] using width.symm) x

/-- Run the rank-seven COPY on a prepared bank using the scheduled recursive
child. Split, pack, execute, unpack and merge at the caller's COPY positions. -/
theorem activeCopyWorker {U : Type} {Q price : ℕ} (child : Descriptor) (w W : ℕ)
    (width : child.width = 7*(w+1)) (positive : 0 < W) (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*(W*142080)))
    (coords : CopyIntervalPositions child (w+1) (W*142080) position)
    (recursive : PackedDescriptorHandoff U Q child price) :
    let V := (prime^(w+1))^16*W
    let m := (prime^(w+1))^16*(W*142080)
    ∃ (P : Type) (H : ℕ) (slot : Fin H) (host : P → Pr P H Q prime U)
      (program : Pr P H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + ((21*(w+1)+13) +
          (intervalChildToll U 0 7 w W 8 + price + (149*(V*142080)*(intervalSplitTapes+5)+6))) ∧
        z.user = u.user ∧ RecordPayload slot (fun _ => blank) 0 y F ∧
          ∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k := by
  intro V m
  obtain ⟨aligned,call⟩ := recursive
  have count := Fintype.card_congr position
  simp only [Fintype.card_fin,← Nat.mul_assoc] at count
  have perRow : volume prime child / 142080 = V := by rw [count,Nat.mul_div_cancel _ (by decide)]
  rw [perRow] at call
  obtain ⟨P,B,body,code,src,dst,seed,worker⟩ := call
  let lane := phaseIntervalChild 0 7 (w+1) W 8
  have widthAt : lane.width = 64*(child.width/64) := by
    rw [Nat.mul_div_cancel' aligned,width]; rfl
  obtain ⟨H,host,program,bank,stock,run⟩ := packedInterval_exec capacity mergeCap (by decide : 0 ≤ 7)
    (by decide : 7 ≤ 8) positive widthAt worker
  refine ⟨_,H,bank 0,host,program,stock,?_⟩
  let wide := {lane with afterD := lane.afterD*142080}
  have size : volume prime lane = V := phaseIntervalChild_volume (by decide) (by decide) _ _
  have interleave : volume prime lane*142080 = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
  have physical : volume prime wide = m := by rw [← interleave,size]; exact Nat.mul_assoc _ _ _
  apply transportWorker physical _ host program stock (fun x y => ∀ k, y (position k) =
    Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k)
  intro x u S left right ready
  obtain ⟨z,F,n,exec,paid,user,result⟩ := run x u S left
    (right.trans (castWord interleave (fun k => SparseRoleCircuit.encode (x k))).symm) ready
  refine ⟨z,F,n,Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x,exec,?_,user,?_,?_⟩
  · rw [← size]; exact paid
  · exact castPayload interleave _ _ _ (mergedPayload bank F _ _ result)
  · exact copyIntervalRead width position coords physical x

end IntegerMultBounds.MathlibTM2.M6.BitNode
