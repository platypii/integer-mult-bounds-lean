module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScan

/-! Prepare the physical selector input required by the classified PR589 scanner. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout Matrix IntegerMultBounds.Swap.Modular

theorem ordinarySelectors_exec {m k Q extra w Bcount W H J : ℕ} {F U : Type}
    (body : F → Pr F (66+extra) Q prime U) (P : Matrix (Fin m) (Fin m) ℚ)
    (v : Descriptor) (parent : Fin m → ZMod (prime^(w+1)))
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin k) (Fin k) (ZMod prime))
    (directory : Descriptor) (dirPositive : directory.Positive) (shape : directory.beforeH = Bcount*prime^(m*((w+1)*m)))
    (room : m*m+m*m ≤ extra) :
    let proj := reduce (prime^(w+1)) P
    let rankFits := P.rank_le_height
    let K := 66+extra
    let caller := Fin.castAddEmb (n := 66) extra
    let mask := caller 57
    let mode := caller 56
    let parents := caller 50
    let rs := residuePairs (m*m) room
    let high := prime^w
    let allLabels := List.range (LabelMask.records directory)
    let schedules := fun xs : List ℕ => xs.flatMap fun j =>
      if fallbackBit rankFits proj (physicalLabel m (w+1) j) then residualSchedule (A := prime) (table (LabelStock.residue m (w+1) 1 j)) else []
    let liveWords := allLabels.map fun j => bitSymbol (a := prime) (LabelStock.live m (w+1) 1 j)
    let badWords := allLabels.map fun j => bitSymbol (a := prime) (fallbackBit rankFits proj (physicalLabel m (w+1) j))
    let privateTapes := (List.finRange K).filter fun i => 58 ≤ i.val
    ∃ selectors : Pr F K Q prime U, ∀ (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
      (initialUser : HS K Q prime U) (initialState : Stacks K prime),
    let clean := {initialState with
      L := fun i => if i ∈ privateTapes then [] else initialState.L i
      R := fun i => if i ∈ privateTapes then [] else Function.update initialState.R (caller 54) (schedules allLabels) i}
    (∀ i : Fin K, 58 ≤ i.val → initialState.R i = []) →
    DirectoryScanInput v P w W H J parent prefixes tail allLabels (fun i => initialState.R (caller (i.castAdd 8))) →
    (initialState.R (caller 29)).length = directory.beforeRows → (initialState.R (caller 30)).length = directory.rows →
    (initialState.R (caller 31)).length = directory.beforeH → initialState.R parents = [] →
    initialState.R mask = [] → initialState.R mode = [] → initialState.R (caller 54) = [] →
    ∃ z D n, z.user = initialUser.user ∧ n ≤ (26*high+4) +
      ((44*allLabels.length+13*(w+1)+16)+3*((6+10*(m*m))*allLabels.length+4)+(2*(directory.beforeRows*directory.rows*Bcount)+2)) +
      ((privateTapes.map fun i => 4*(initialState.L i).length).sum+privateTapes.length*(2*high+4)+1) ∧
      Exec body selectors (mk initialUser initialState) n (mk z D) ∧
      DirectoryReady v P w W H J parent prefixes tail schedules D allLabels ∧
      D.L (caller 24) = initialState.L (caller 24) ∧ D.R (caller 24) = initialState.R (caller 24) ∧
      D.R (caller 48) = initialState.R (caller 48) ∧ D.R mask = liveWords ∧ D.R mode = badWords := by
  intro proj rankFits K caller mask mode parents rs high allLabels schedules liveWords badWords privateTapes
  obtain ⟨writer,controls⟩ := Cover.Fallback.directoryControls_exec body rankFits
    ((LabelRing.res prime (w+1) (by omega)).mapMatrix proj) table proj rfl directory dirPositive shape room
  let init : Pr F K Q prime U := (Node.expProg 0 prime (caller 28) (caller 45) (caller 58) (caller 59) (caller 60) (caller 61)).seq
    (Node.scanR (caller 58) (caller 59) (LabelCountBank.pushAll (rs.map Prod.fst)))
  refine ⟨(init.seq writer).seq (clearWorkTapes privateTapes),?_⟩
  intro prefixes tail initialUser initialState clean freePrivate inputs
    beforeRows rows beforeH parentsFree maskFree modeFree queueFree
  have ready := directoryReady_of_inputs schedules allLabels initialState inputs.archive inputs.widths inputs.headers
  have raw (i : Fin 66) (hi : i.val < 58) (off : i ≠ 54) : clean.R (caller i) = initialState.R (caller i) := by
    simp [clean,privateTapes,show ¬58 ≤ (caller i).val from Nat.not_le_of_gt hi,Function.update_of_ne (caller.injective.ne off)]
  obtain ⟨_,_,_,_,_,_,one,_,_,_,ticks,_⟩ := (show DirectoryReady _ _ _ _ _ _ _ _ _ _ _ _ from ready)
  obtain ⟨z,n,user,price,run⟩ := controls initialUser initialState freePrivate
    ((congrArg List.length (raw 28 (by decide) (by decide))).symm.trans ((congrArg List.length one).trans (length_binSyms ..)))
    ((congrArg List.length (raw 45 (by decide) (by decide))).symm.trans ticks)
    beforeRows rows beforeH parentsFree maskFree modeFree queueFree
  let liveState := {clean with R := Function.update clean.R mask liveWords}
  let D := {liveState with R := Function.update liveState.R mode badWords}
  have liveReady := DirectoryReady.updateSelector 57 (by decide) (by decide) liveWords ready
  have finalReady := DirectoryReady.updateSelector 56 (by decide) (by decide) badWords liveReady
  have keep (i : Fin 66) (hi : i.val < 58) (h : i ≠ 54) (b : i ≠ 56) (l : i ≠ 57) :
      D.R (caller i) = initialState.R (caller i) :=
    (Function.update_of_ne (caller.injective.ne b) ..).trans
      ((Function.update_of_ne (caller.injective.ne l) ..).trans (raw i hi h))
  refine ⟨z,D,n,user,price,run,finalReady,?_,keep 24 (by decide) (by decide) (by decide) (by decide),
    keep 48 (by decide) (by decide) (by decide) (by decide),?_,Function.update_self mode badWords liveState.R⟩
  · simp [D,liveState,clean,privateTapes,caller]
  · exact (Function.update_of_ne (caller.injective.ne (by decide : (57 : Fin 66) ≠ 56)) badWords liveState.R).trans (Function.update_self mask liveWords clean.R)

end IntegerMultBounds.MathlibTM2.M6.BitNode
