module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafFrame
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Routines

/-! Install the six parent descriptor tapes from reusable caller words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem prepareRecordHeaders_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (v : RecursiveInterchangeLayout.Descriptor) (src : Fin 6 → Fin T) (dst : Fin 6 ↪ Fin T)
    (tmp aux : Fin T) (apart : ∀ i j, src i ≠ dst j) (ports : ∀ i, [src i,dst i,tmp,aux].Nodup)
    (u : HS T Q prime U) (S : Stacks T prime)
    (words : ∀ i, S.R (src i) = (Routines.hdr v i).map bitSymbol)
    (free : ∀ i, S.L (dst i) = [] ∧ S.R (dst i) = []) (ht : S.R tmp = []) (ha : S.R aux = []) :
    let fields := List.finRange 6
    ∃ z D, z.user = u.user ∧ Exec body
      ((Record.copyLeafHeaders src dst tmp aux fields).seq (.act (pushMarkers (fields.map dst))))
      (mk u S) (((fields.map fun i => 6*(S.R (src i)).length+6).sum+1)+1) (mk z D) ∧
      (∀ i x, CounterDimensions.descriptorTape prime (some (Routines.hdr v i)) x =
        readAt blank (D.L (dst i)) (D.R (dst i)) (x-1)) ∧
      ∀ j, (∀ i, dst i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro fields
  obtain ⟨z,B,user,copy,left,loaded,off⟩ := Record.copyLeafHeaders_exec body src dst tmp aux apart ports
    fields (List.nodup_finRange _) u S ht ha (fun i _ => (free i).2)
  have mark := Exec.act (body := body) (pushMarkers (fields.map dst)) (mk z B)
  rw [pushMarkers_run _ ((List.nodup_finRange _).map dst.injective)] at mark
  refine ⟨z,_,user,Exec.seq copy mark,?_,?_⟩
  · intro i x
    have mem := List.mem_map_of_mem (f := dst) (List.mem_finRange i)
    simp only [ite_eq_left mem,left,(free i).1,loaded i (List.mem_finRange i),words]
    change RadixZeroFill.encodedBinary _ x = _
    rw [encodedBinary_eq,readAt_single]
  · intro j outside
    have absent : j ∉ fields.map dst := fun h => by
      obtain ⟨i,_,eq⟩ := List.mem_map.mp h
      exact outside i eq
    exact ⟨(ite_eq_right absent).trans (congrFun left j),off j (fun i _ => outside i)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
