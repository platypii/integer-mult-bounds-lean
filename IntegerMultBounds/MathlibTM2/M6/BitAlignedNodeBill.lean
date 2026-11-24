module

public import IntegerMultBounds.MathlibTM2.M6.BitScheduledIdleInterval
public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitIdleChartHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitChildDirectoryBill

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host M8.RevMachine
open IntegerMultBounds.Networks Certificates.PR589 RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Charge an assembled node once per scheduled child. The local prices
exclude recursive work and the dispatch overhead already paid on idle calls. -/
theorem alignedNodeDirectoryBill (node : Descriptor) (width : 64 ∣ node.width)
    (rows : 142080 ∣ node.rows) (time : ℕ → ℕ)
    (sweep idle sweepLocal idleLocal : Fin 9 → ℕ)
    (dispatch : Fin 9 → Fin idleCopies.length → ℕ)
    (sweeps : ∀ i, sweep i ≤ sweepLocal i+((List.range' (stageChildStart i)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map time).sum)
    (remainders : ∀ i, idle i ≤ idleLocal i+∑ j, dispatch i j)
    (calls : ∀ i j, dispatch i j ≤ 2*volume prime (scheduledChild prime node (idleDirectoryIndex (i,j)))+
      time (idleDirectoryIndex (i,j)).val) :
    (∑ i, sweep i)+(∑ i, idle i) ≤
      (∑ i, sweepLocal i)+(∑ i, idleLocal i)+5*volume prime node+(∑ j : Fin nodeChildren5.length, time j.val) := by
  have stages := Finset.sum_le_sum (s := Finset.univ) (fun i _ => sweeps i)
  have idleCalls := Finset.sum_le_sum (s := Finset.univ) (fun i _ => remainders i)
  rw [Finset.sum_add_distrib] at stages idleCalls
  have localBill := alignedIdleDispatch_sum node width rows dispatch _ calls
  have partition := nodeChildDirectoryBill time
  omega

/-- Assemble a single transpose program across runtime sizes from sweeps and
individual idle interval workers. The node pays for each directory child once. -/
theorem alignedPackedNodeFamily {U Config : Type} :
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ rate : ℕ, ∀ w W : Config → ℕ,
    let V := fun c => (prime^(w c))^128*W c
    (∀ c, 0 < V c) → ∀ (layout : Config → Descriptor) (time : Config → ℕ → ℕ)
      (sweep localCost : Config → Fin 9 → ℕ) (dispatch : Config → Fin nodeChildren5.length → ℕ),
    (∀ c, 64 ∣ (layout c).width) → (∀ c, 142080 ∣ (layout c).rows) →
    (∀ c i, sweep c i ≤ localCost c i+((List.range' (stageChildStart i)
      (stageRuns.flatMap (fun _ => Geometry.Moves.localPaid)).length).map (time c)).sum) →
    (∀ c i j, let k := idleDirectoryIndex (i,j)
      dispatch c k ≤ 2*volume prime (scheduledChild prime (layout c) k)+time c k.val) →
    (∀ i, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithCharge cleanupWeight (V c) (fun x y => ∀ j : Fin (W c),
        let addr := fun z => flatWindowEquiv (w c) (W c) (windowState (w c) z,j)
        readRoles addr y = (Piece.stage i).run (readRoles addr x)) body code src dst (seed c) (sweep c i)) →
    (∀ (i : Fin 9) (k : (Fin 32 × Fin 5) × Fin 222), ∃ (T : ℕ) (P : Type) (slot : Fin T)
      (body : P → Pr P T Q prime U) (code : Pr P T Q prime U) (seed : Config → Stacks T prime),
      ∀ c (word : Fin (V c) → ZMod 2) v D, D.L slot = [] →
        D.R slot = List.ofFn (fun j => SparseRoleCircuit.encode (word j)) →
        (∀ j, j ≠ slot → D.L j = (seed c).L j ∧ D.R j = (seed c).R j) →
        ∃ z F n y, Exec body code (mk v D) n (mk z F) ∧
          (∀ js : List _, js.Nodup → n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+
            dispatch c (idleDirectoryIndex (i,idleCopyIndex k))) ∧ z.user = v.user ∧
          Cover.Fallback.RecordPayload slot (fun _ => blank) 0 y F ∧ parentIntervalRead i k.2 (w c) (W c) word y) →
    ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst, ∃ seed : Config → Stacks T prime,
      ∀ c, PackedPieceHandoffWithCharge cleanupWeight (V c) (packedChildOutput (w c) (V c)) body code src dst (seed c)
        ((∑ i, localCost c i)+9*(1+(142081*(10*V c+10)+1))+5*volume prime (layout c)+rate*V c+2+
          ∑ j : Fin nodeChildren5.length, time c j.val) := by
  classical
  obtain ⟨states,build⟩ := assembledFlatNodeFamily (U := U) (Config := Config)
  refine ⟨states,?_⟩
  intro Q fits
  obtain ⟨rate,assemble⟩ := build fits
  refine ⟨rate,?_⟩
  intro w W V positive layout time sweep localCost dispatch width rows stages calls sweeps workers
  let overhead c := 1+(142081*(10*V c+10)+1)
  let idle c (i : Fin 9) := (∑ j : Fin idleCopies.length, dispatch c (idleDirectoryIndex (i,j)))+overhead c
  obtain ⟨P,T,body,code,src,dst,seed,run⟩ := assemble w W V (fun _ => rfl) positive (fun _ => Equiv.refl _)
    sweep idle sweeps (by
      intro i
      choose tapes P slot inner code seed each using workers i
      obtain ⟨H,host,worker,src,dst,origin,_,prep⟩ := uniformRemainderWindow (U := U) i tapes P slot inner code
      have installed c := prep (w c) (W c) (fun k => seed k c) (dispatch c) (fun k => each k c)
      refine ⟨_,H,host,worker,src,dst,fun c => idleWindowSeed origin (fun k => seed k c),?_⟩
      intro c
      simpa only [idle,overhead,V,Equiv.refl_apply,Fin.cast_refl,id_eq,Nat.add_assoc] using installed c)
  refine ⟨P,T,body,code,src,dst,seed,?_⟩
  intro c x u S words fresh
  obtain ⟨z,F,n,y,exec,paid,rest⟩ := run c x u S words fresh
  refine ⟨z,F,n,y,exec,?_,rest⟩
  intro js unique
  have h := paid js unique
  have bound := alignedNodeDirectoryBill (layout c) (width c) (rows c) (time c) (sweep c) (idle c)
    (localCost c) (fun _ => overhead c) (fun i j => dispatch c (idleDirectoryIndex (i,j))) (stages c)
    (fun i => (Nat.add_comm _ _).le) (calls c)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,overhead] at bound
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
