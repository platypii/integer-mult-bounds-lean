module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapDimensions
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Family

/-! Initialize the coordinate loop counters from the caller clock and the fixed network rank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FlatCoordinateSchedule (bits)
variable {T Q : ℕ} {P U : Type}

def leafCounterPorts {K : ℕ} (aux : Fin 24 ↪ Fin K) : Fin 8 ↪ Fin (66+K) :=
  let privatePort := ((Fin.castLEEmb (by decide : 7 ≤ 24)).trans aux).trans (Fin.natAddEmb 66)
  ⟨Fin.cons ((45 : Fin 66).castAdd K) privatePort,by
    intro i j eq
    have ne (k : Fin 7) : (45 : Fin 66).castAdd K ≠ privatePort k := by
      intro h
      have hit := congrArg Fin.val h
      change 45 = 66+_ at hit
      omega
    cases i using Fin.cases <;> cases j using Fin.cases <;> simp_all [privatePort.injective.eq_iff,fun k => (ne k).symm]⟩

def leafCounterMarkers : List (Fin 24) := [0,1,2,3,4,5,7,9,10,11,15]

noncomputable def installLeafCounters (aux : Fin 24 ↪ Fin T) (arity rank : ℕ) : Act T Q prime U :=
  let put := fun i n => LabelCycle.pushWord (aux i) ((bits n).map bitSymbol)
  put 5 (rank/arity) (put 9 rank (put 10 arity (put 11 rank (put 15 1
    (pushMarkers (leafCounterMarkers.map aux))))))

theorem prepareLeafCounters_exec (body : P → Pr P T Q prime U) (aux : Fin 24 ↪ Fin T)
    (r : Fin 8 ↪ Fin T) (shared : r 1 = aux 0) (arity rank w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (clock : (S.R (r 0)).length = w)
    (free : ∀ i : Fin 8, i ≠ 0 → S.R (r i) = [])
    (empty : ∀ i, S.L (aux i) = [] ∧ S.R (aux i) = []) :
    ∃ z D n, z.user = u.user ∧ n ≤ 21*(w+1)+13 ∧
      Exec body ((swapExponent r).seq (.act (installLeafCounters aux arity rank))) (mk u S) n (mk z D) ∧
      RepT (CommonBank.counters (Family.leafC (w+1) arity rank rank)) (D.L ∘ aux) (D.R ∘ aux) ∧
      ∀ j, (∀ i, aux i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  obtain ⟨z,n,user,time,run⟩ := swapExponent_exec body r w u S clock free
  rw [shared] at run
  let D := {S with R := Function.update S.R (aux 0) ((bits (w+1)).map bitSymbol)}
  have install := Exec.act (body := body) (installLeafCounters aux arity rank) (mk z D)
  simp only [installLeafCounters,LabelCycle.pushWord_run,pushMarkers_run _ ((by decide : leafCounterMarkers.Nodup).map aux.injective)] at install
  refine ⟨z,_,_,user,by omega,Exec.seq run install,?_,?_⟩
  · intro i x
    have repr (o : Option (List Bool)) : CounterDimensions.descriptorTape prime o x =
        readAt blank (o.toList.map (fun _ => separator)) ((o.getD []).map bitSymbol) (x-CounterDimensions.descriptorHead o) := by
      cases o with
      | none => simp [CounterDimensions.descriptorTape,CounterDimensions.descriptorHead,readAt_nil_left,wordTape_nil]
      | some xs => change RadixZeroFill.encodedBinary xs x = readAt blank [separator] _ (x-1)
                   rw [encodedBinary_eq,readAt_single]; rfl
    have left (j) := (empty j).1
    have right (j) := (empty j).2
    specialize repr (CommonBank.word (Family.leafC (w+1) arity rank rank i))
    rw [show (CommonBank.counters (Family.leafC (w+1) arity rank rank)).tape i x = _ from repr]
    have updateAux (R : Fin T → List (Fin (prime+4))) (j : Fin 24) (xs : List (Fin (prime+4))) (i : Fin 24) :
        Function.update R (aux j) xs (aux i) = if i = j then xs else R (aux i) := by
      by_cases h : i = j <;> simp [h,aux.injective.eq_iff]
    have marker : aux i ∈ leafCounterMarkers.map aux ↔ i ∈ leafCounterMarkers := by simp
    simp only [Function.comp_apply,D,updateAux,left,right,marker]
    congr 1
    · fin_cases i <;> rfl
    · fin_cases i <;> first | rfl | (simp (disch := decide); rfl)
  · intro j off
    have absent : j ∉ leafCounterMarkers.map aux := by
      intro mem; obtain ⟨i,_,eq⟩ := List.mem_map.mp mem; exact off i eq
    simp [D,absent,Function.update_of_ne,fun i => (off i).symm]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
