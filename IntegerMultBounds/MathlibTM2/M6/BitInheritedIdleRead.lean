module

public import IntegerMultBounds.MathlibTM2.M6.BitInheritedReturnMerge
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleWindow

/-! Interpret the interleaved recursive output at the exact cells of a selected idle window. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks RecursiveInterchangeLayout
open Stack Host
open Shared50ModularControl (prime)

private theorem castTransposeRead {v u : Descriptor} (same : v = u) {V : ℕ}
    (sv : volume prime v = V) (su : volume prime u = V) (x : Fin (volume prime v) → ZMod 2) (a : Fin (volume prime u)) :
    Shared50RecursiveNodeRows.transpose (one_dvd v.rows) x
      ((a.cast su).cast sv.symm) =
    Shared50RecursiveNodeRows.transpose (one_dvd u.rows) (fun b => x ((b.cast su).cast sv.symm)) a := by
  subst u
  rfl

theorem idleInterleaved_read (i : Fin 9) (j : Fin 222) (w W : ℕ) :
    let e := idleInterval i j
    let lane := phaseIntervalChild e.1 e.2 w W 64
    let wide := {lane with afterD := lane.afterD*142080}
    let size := intervalChild_volume (idleBounds i j).1 ((idleBounds i j).2.trans (by decide : 63 ≤ 64)) w (W*142080)
    let shape : wide = phaseIntervalChild e.1 e.2 w (W*142080) 64 := by
      simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
    let physical := (congrArg (volume prime) shape).trans size
    ∀ x : Fin (volume prime wide) → ZMod 2,
      intervalChildRead i j w (W*142080) (fun k => x (k.cast physical.symm)) (fun k =>
        Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x
          (k.cast physical.symm)) := by
  intro e lane wide size shape physical x a
  exact castTransposeRead shape physical size x a

def IntervalRun {P U : Type} {N Q : ℕ} (seed : Stacks N prime) (price : ℕ) (lane : Descriptor)
    (reads : let wide := {lane with afterD := lane.afterD*142080}
             (Fin (volume prime wide) → ZMod 2) → (Fin (volume prime wide) → ZMod 2) → Prop) : Prop :=
    let T := intervalSplitTapes
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U) (program : Pr (Empty ⊕ P) H Q prime U)
      (bank : Fin T ↪ Fin H), bank 0 = caller 0 ∧
    ∀ (x : Fin (volume prime wide) → ZMod 2) u S,
      S.R (caller 0) = List.ofFn (fun k : Fin (V*142080) => SparseRoleCircuit.encode (x (k.cast size))) →
      (∀ k, S.L (caller k) = []) → (∀ k, k ≠ 0 → S.R (caller k) = []) →
      (∀ k : Fin 142082, let t := (k.castAdd T).castAdd N
        S.L t = [] ∧ S.R t = []) →
      (∀ k : Fin N, let t := k.natAdd (142082+T)
        S.L t = seed.L k ∧ S.R t = seed.R k) →
      ∃ z F n, ∃ y : Fin (volume prime wide) → ZMod 2, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(T+5)+5)*(V*142080)+24+((142081*(8*V+10)+1+price)+(149*(V*142080)*(T+5)+6)) ∧
        z.user = u.user ∧ reads x y ∧
        RepT (intervalOwnerBank (putWord (fun _ => blank) 0 (List.ofFn fun k : Fin (V*142080) =>
          SparseRoleCircuit.encode (y (k.cast size)))) (fun r k => y ((finProdFinEquiv (k,r)).cast size)))
          (embStk bank F).L (embStk bank F).R

private theorem intervalRun_of_transpose {P U : Type} {N Q price : ℕ} (lane : Descriptor)
    (positiveV : 0 < volume prime lane)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed}
    (child : PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price) :
    let wide := {lane with afterD := lane.afterD*142080}
    ∀ reads, (∀ x, reads x (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x)) →
      IntervalRun (P := P) (U := U) (Q := Q) seed price lane reads := by
  intro wide reads effect
  obtain ⟨host,program,bank,target,run⟩ := inheritedInterval_exec lane positiveV capacity child
  refine ⟨host,program,bank,target,?_⟩
  intro x u S source left empty fresh prepared
  obtain ⟨z,F,n,exec,paid,user,rows⟩ := run x u S source left empty fresh prepared
  refine ⟨z,F,n,Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x,exec,paid,user,effect x,rows⟩

private theorem intervalVolume_pos {lo hi W : ℕ} (ordered : lo ≤ hi) (fits : hi ≤ 64)
    (w : ℕ) (positive : 0 < W) : 0 < volume prime (phaseIntervalChild lo hi w W 64) := by
  rw [intervalChild_volume ordered fits]
  exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive

/-- The physical split, recursive child and merge discharge the chart's
single-copy read condition when the trailing spectator contains whole rows. -/
theorem inheritedIdleCopy_exec {P U : Type} {N Q price : ℕ}
    (i : Fin 9) (j : Fin 222) (w W : ℕ) (positive : 0 < W)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed} :
    let e := idleInterval i j
    let lane := phaseIntervalChild e.1 e.2 w W 64
    PackedPieceHandoff (volume prime lane) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price →
    let wide := {lane with afterD := lane.afterD*142080}
    let shape : wide = phaseIntervalChild e.1 e.2 w (W*142080) 64 := by
      simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
    let physical := (congrArg (volume prime) shape).trans
      (intervalChild_volume (idleBounds i j).1 ((idleBounds i j).2.trans (by decide : 63 ≤ 64)) w (W*142080))
    IntervalRun (P := P) (U := U) (Q := Q) seed price lane (fun x y =>
      intervalChildRead i j w (W*142080) (fun k => x (k.cast physical.symm)) (fun k => y (k.cast physical.symm))) := by
  intro e lane child wide shape physical
  have positiveV := intervalVolume_pos (idleBounds i j).1
    ((idleBounds i j).2.trans (by decide : 63 ≤ 64)) w positive
  apply intervalRun_of_transpose lane positiveV capacity child
  intro x
  exact idleInterleaved_read i j w W x

end IntegerMultBounds.MathlibTM2.M6.BitNode
