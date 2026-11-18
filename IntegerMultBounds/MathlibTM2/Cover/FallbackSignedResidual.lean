module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDiagonalRewind
public import IntegerMultBounds.MathlibTM2.Cover.FallbackForwardReady

/-! Execute a residual matrix from its packed coefficients and round-trip pivot schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def signedResidual (d : ℕ) : Pr P (N+2) columnCapacity prime U :=
  .seq (streamedItinerary (d+1) prime forwardBank (Fin.last N).castSucc (d+1)) (diagonalRewind d)

theorem signedResidual_exec (rows : Fin (d+1) → Fin (d+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (valid : Itinerary.Valid rows m (d+1)) (s : (ZMod M)ˣ)
    (sign : (Itinerary.run rows m (d+1)).det = (s : ZMod M)) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) (original : Fin (M^(d+1)*W) → ZMod 2) :
    let bank := fun n => columnBank.trans (archivePorts n)
    let ready := fun n t => ColumnReady (bank n) H J (Itinerary.run rows m n) t SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    let anchor := fun x j => ((Fin.cons s (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    let schedule := orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest
    let pairCost := ((List.finRange d).map fun i => pairScalingTime U i.succ 0 i.succ w W H J).sum
    let stepCost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
    let forwardCost := (d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1
    ready 0 tail anchor S → clean S → S.R (Fin.last N).castSucc = scheduleCode rows ++ schedule →
    ∃ z F n, z.user = v.user ∧ n ≤ forwardCost + ((1+(pairCost+1))+((d+1)*stepCost+1)) ∧
      Exec body (signedResidual d) (mk v S) n (mk z F) ∧ ready 0 tail (fun x => m.mulVec x) F ∧
      clean F ∧ F.R (Fin.last N).castSucc = rest ∧ F.R (bank 1 34) = S.R (bank 1 34) := by
  intro bank ready clean anchor schedule pairCost stepCost forwardCost before free code
  obtain ⟨u,D,l,suffix,hu,hl,forward,next,freeD,stream,archive⟩ :=
    forwardReady_exec rows H J hm body v S m valid tail schedule dest q original anchor before free code
  let finalMatrix := Itinerary.run rows m (d+1)
  obtain ⟨_,_,_,cleared,units⟩ := Itinerary.run_spec rows m (d+1) le_rfl valid
  let a := fun j : Fin (d+1) => (units j j.isLt).unit
  have diag : finalMatrix = Matrix.diagonal (fun j => (a j : ZMod M)) := by
    ext i j
    by_cases h : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
      exact (units i i.isLt).unit_spec.symm
    · rw [Matrix.diagonal_apply_ne _ h]
      exact cleared i j j.isLt h
  have prod : ∏ j, a j = s := by
    apply Units.ext
    rw [Units.coe_prod,← Matrix.det_diagonal,← diag]
    exact sign
  obtain ⟨z,F,n,hz,hn,rewind,result⟩ := diagonalRewind_exec rows m valid a diag s prod H J hm hw hW
    body u D tail (S.R (bank 1 34)) suffix rest dest q empty original next freeD stream archive
  exact ⟨z,F,l+n,hz.trans hu,Nat.add_le_add hl hn,Exec.seq forward rewind,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
