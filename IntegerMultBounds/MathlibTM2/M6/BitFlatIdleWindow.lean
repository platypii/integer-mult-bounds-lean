module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleChild
public import IntegerMultBounds.MathlibTM2.M6.BitSweepNodeAddress
public import IntegerMultBounds.MathlibTM2.M6.BitPortCorrectionSeed

/-! Place all remainder charts around the interval children on the permanent bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589 Certificates.PR589.Nine
open Cover
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open M8.RevMachine
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

theorem idleBounds (i : Fin 9) (j : Fin 222) :
    (idleInterval i j).1 ≤ (idleInterval i j).2 ∧ (idleInterval i j).2 ≤ 63 := by
  obtain ⟨lo,hi,_⟩ := BitHosting.remainder_counts _ (idleInterval_mem i j)
  exact ⟨lo,hi⟩

/-- A child acts on the two contiguous fields of its port. The inherited
spectator is already part of the payload length. -/
def intervalChildRead (i : Fin 9) (j : Fin 222) (w W : ℕ)
    (x y : Fin ((prime^w)^128*W) → ZMod 2) : Prop :=
  let e := idleInterval i j
  let child := phaseIntervalChild e.1 e.2 w W 64
  let size : volume prime child = (prime^w)^128*W :=
    intervalChild_volume (idleBounds i j).1 ((idleBounds i j).2.trans (by decide)) w W
  ∀ a, y (a.cast size) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun b => x (b.cast size)) a

theorem flatIdleWindow_charts [M8.Machine.Net] (i : Fin 9) :
    ∃ a k tapes states : ℕ, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^128*W
      ∃ A B : OwnerStage V, A.tapes ≤ tapes ∧ B.tapes ≤ tapes ∧ A.states ≤ states ∧ B.states ≤ states ∧
        (∃ S, ChartPrivateReady A S) ∧ (∃ S, ChartPrivateReady B S) ∧
        A.cost+B.cost = a*V+k*(3808274*V+LeafCore.coreCost V w+1)+6*idleCopies.length ∧
        ∀ x y, (∀ j, intervalChildRead i j.2 w W (A.transform x (idleTape i j)) (y (idleTape i j))) →
          (∀ t, (∀ j, t ≠ idleTape i j) → y t = A.transform x t) →
          ∀ j : Fin W, let addr := fun z => flatWindowEquiv w W (windowState w z,j)
            readRoles addr (B.transform y) = (Piece.remainder i.val).run (readRoles addr x) := by
  classical
  let slot : ((Fin 32 × Fin 5) × Fin 222) ↪ Fin 142081 := ⟨idleTape i,idleTape_injective i⟩
  have unique : idleCopies.Nodup := stageRuns_nodup.product (List.nodup_finRange _)
  have mem (j) : j ∈ idleCopies := List.mem_flatMap.mpr ⟨j.1,mem_stageRuns _,List.mem_map.mpr ⟨j.2,List.mem_finRange _,rfl⟩⟩
  choose a k entry exit build using fun j : (Fin 32 × Fin 5) × Fin 222 =>
    flatIdleChild_charts (port (idleRole i j).port.val) (port_checked _ (idleRole i j).port.isLt)
      _ _ (idleBounds i j.2).1 (idleBounds i j.2).2
  let tapes := fun (m : _ → SharedBankSkeleton.Skeleton 1 prime) =>
    142081+(idleCopies.map fun j => 142081+((m j).tapes+142080)).sum
  let states := fun (m : _ → SharedBankSkeleton.Skeleton 1 prime) => (idleCopies.map fun j => (m j).states).sum+1
  refine ⟨(idleCopies.map a).sum,(idleCopies.map k).sum,max (tapes entry) (tapes exit),max (states entry) (states exit),?_⟩
  intro w W hw hW V
  choose pre post fp fq sp sq cost act using fun j => build j w W hw hW
  obtain ⟨A,sa,ta,qa,ca,ra,oa⟩ := compileSeededPorts slot pre idleCopies unique (fun j _ => sp j)
  obtain ⟨B,sb,tb,qb,cb,rb,ob⟩ := compileSeededPorts slot post idleCopies unique (fun j _ => sq j)
  have pt j := congrArg SharedBankSkeleton.Skeleton.tapes (fp j)
  have qt j := congrArg SharedBankSkeleton.Skeleton.tapes (fq j)
  have ps j := congrArg SharedBankSkeleton.Skeleton.states (fp j)
  have qs j := congrArg SharedBankSkeleton.Skeleton.states (fq j)
  change ∀ j, (pre j).tapes = (entry j).tapes at pt
  change ∀ j, (post j).tapes = (exit j).tapes at qt
  change ∀ j, (pre j).states = (entry j).states at ps
  change ∀ j, (post j).states = (exit j).states at qs
  refine ⟨A,B,by simpa only [ta,tapes,pt] using le_max_left (tapes entry) (tapes exit),
    by simpa only [tb,tapes,qt] using le_max_right (tapes entry) (tapes exit),
    by simpa only [qa,states,ps] using le_max_left (states entry) (states exit),
    by simpa only [qb,states,qs] using le_max_right (states entry) (states exit),sa,sb,?_,?_⟩
  · have total := congrArg (fun f : ((Fin 32 × Fin 5) × Fin 222 → ℕ) => (idleCopies.map f).sum) (funext cost)
    simp only [List.sum_map_add,List.sum_map_mul_right,List.map_const',List.sum_replicate,nsmul_eq_mul] at total
    rw [ca,cb]
    dsimp only [V] at *
    simp only [Nat.cast_id] at total
    omega
  · intro x y children off j addr
    let pack := fun (v : Axis ⊕ Axis → ZMod (prime^w)) => flatWindowEquiv w W ((v ∘ Sum.inl,v ∘ Sum.inr),j)
    apply idleCopies_modular_read w i pack x (B.transform y)
    · intro t e P v
      let s := (v ∘ Sum.inl,v ∘ Sum.inr)
      have ch := children t
      change intervalChildRead i t.2 w W (A.transform x (slot t)) (y (slot t)) at ch
      rw [ra x t (mem t)] at ch
      have h := act t (x (slot t)) (y (slot t)) ch s j
      change B.transform y (slot t) _ = _
      rw [rb y t (mem t)]
      dsimp only [pack,P,e]
      rw [idleExchange_blocks _ (port_checked _ (idleRole i t).port.isLt),Matrix.fromBlocks_mulVec]
      exact h
    · intro t away
      have miss (u) (_ : u ∈ idleCopies) : slot u ≠ t := (away u).symm
      exact (ob y t miss).trans ((off t away).trans (oa x t miss))

end IntegerMultBounds.MathlibTM2.M6.BitNode
