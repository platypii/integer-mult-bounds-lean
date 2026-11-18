module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchivePorts
public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchiveStep

/-! Run physical reverse columns from the two alternating matrix archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def reverseStages (d : ℕ) : ℕ → Pr P (N+2) columnCapacity prime U
  | 0 => .act .done
  | n+1 => if h : n < d then
      .seq (placedColumn (archivePorts n) (⟨n,h⟩ : Fin d))
        (.seq (dropWords (archivePorts n (columnBank 2)) (archivePorts (n+1) (columnBank 34))
          (archivePorts n (columnBank 0)) (d*d)) (reverseStages d n))
    else reverseStages d n

/-- At every positive stage the exposed matrix supplies the column coefficients. -/
theorem reverseStage_exec (k : Fin d) (rows : Fin d → Fin d) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m (k.val+1))
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2)
    (code : S.R (Fin.last N).castSucc = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let ports := archivePorts k.val
    let stage := Itinerary.run rows m
    let ready := ColumnReady (columnBank.trans ports) H J (stage k.val) tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    ready (fun x => stage (k.val+1) *ᵥ x) S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+columnProgramTime U k (rows k) w W H J ∧
      Exec body (placedColumn ports k) (mk v S) n (mk z F) ∧ ready (fun x => stage k.val *ᵥ x) F ∧ clean F ∧
      F.R (Fin.last N).castSucc = orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest ∧
      F.R (archivePorts (k.val+1) (columnBank 34)) = S.R (archivePorts (k.val+1) (columnBank 34)) := by
  intro ports stage ready clean before free
  have unit := ((Itinerary.valid_succ rows m k.val).mp valid).2 k.isLt
  obtain ⟨z,F,n,hz,hn,run,next,freeF,stream,frame⟩ := placedColumn_exec ports k rows H J hm hw hW body v S
    (stage k.val) unit.2 tail rest dest q empty original (fun x => stage k.val *ᵥ x)
    (by simpa [ports,archivePorts_stream] using code)
    (by simpa only [ready,stage,Itinerary.run_succ rows m k.val k.isLt,← mulVec_mulVec] using before)
    (fun i hi => by simpa only [ports,archivePorts_workspace _ _ hi] using free i hi)
  exact ⟨z,F,n,hz,hn,run,next,fun i hi => by simpa only [ports,archivePorts_workspace _ _ hi] using freeF i hi,
    by simpa only [ports,archivePorts_stream] using stream,(frame _ (archivePorts_other k.val)).2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
