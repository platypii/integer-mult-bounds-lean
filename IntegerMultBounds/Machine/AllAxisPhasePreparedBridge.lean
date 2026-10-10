import IntegerMultBounds.Machine.AllAxisPhaseOriginalMetadata

/-! The physically prepared original-header phase bank is literally the
source-sharing bank required by the aggregate polynomial phase machine.
Only the original native source is shared; immutable ell is physically copied. -/
namespace IntegerMultBounds.Machine.AllAxisPhasePreparedBridge
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ButterflyStreamData (Coefficient)
open Networks.Shared50ModularControl (prime)
open ActivePrefixStageHeadersData (Order)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {a : ℕ}

theorem map_binary (ha : 2≤a) (bs : List Bool) :
    SymbolTriplePlaced.mapTape ha (RadixZeroFill.encodedBinary bs)=
      (RadixZeroFill.encodedBinary bs : ℤ → Fin (a+4)) := by
  funext z
  apply Fin.ext
  rfl

theorem map_bank (ha : 2≤a) (st : ActiveRepairRankHeadersCommands.State) :
    Alphabet.mapTapes (SymbolTriplePlaced.encoding ha) (ActiveRepairRankHeadersCommands.bank (a:=2) st)=
      ActiveRepairRankHeadersCommands.bank (a:=a) st := by
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    induction i using Fin.addCases (m:=28) (n:=15) with
    | right i =>
      simp only [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
        Tapes.append,Fin.addCases_right,SharedBank.empty]
      rfl
    | left i =>
      cases hs : st i with
      | none => simp [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
          ActiveRepairRankHeadersCommands.caller,Tapes.append,hs,SymbolTriplePlaced.encoding,blank]
      | some n =>
        simpa only [Alphabet.mapTapes,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
          ActiveRepairRankHeadersCommands.caller,Tapes.append,Fin.addCases_left,hs] using
          (show (fun z => (SymbolTriplePlaced.encoding ha).encode
            (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n) z))=_ from
            map_binary ha (RecursiveChildQuotientsConstant.bits n))

theorem ready_eq (order : Order) (d : Inputs s) (ell : ℕ)
    (xs : Fin ((d.rows*2^s.bits)*2^ell) → Coefficient) :
    AllAxisPhaseOriginalMetadata.ready order d ell=
      setTape (Alphabet.mapTapes (SymbolTriplePlaced.encoding ActivePrefixStageNative.ha)
        (AllAxisPolynomialPlacement.input order d.stage d.rows ell xs)) 56 (fun _ => blank) 0 := by
  have hb := map_bank ActivePrefixStageNative.ha
    (ActivePrefixStageHeadersData.finished order d.stage d.rows)
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m:=43) (n:=24) with
    | left i =>
      have hn : Fin.castAdd 24 i≠(56 : Fin 67) := by
        intro h; have hv := congrArg (fun x : Fin 67 => x.val) h
        simp only [Fin.val_castAdd] at hv
        have hi := i.isLt; omega
      have he : Fin.castAdd 24 i=Fin.castAdd 1 (Fin.castAdd 6 (Fin.castAdd 17 i)) := Fin.ext rfl
      simp only [Function.update_of_ne hn,Alphabet.mapTapes,Fin.addCases_left]
      rw [he]
      simp only [AllAxisPolynomialPlacement.input,AllAxisPolynomialStreamInit.input,
        AllAxisFullStreamInit.input,AllAxisPhaseStreamInit.input,AllAxisAddressHeaders.initial,
        AllAxisPhaseHeadersData.initial,Tapes.append,Fin.addCases_left]
      rfl
    | right i => fin_cases i <;> rfl
  · funext i
    induction i using Fin.addCases (m:=43) (n:=24) with
    | left i =>
      have hn : Fin.castAdd 24 i≠(56 : Fin 67) := by
        intro h; have hv := congrArg (fun x : Fin 67 => x.val) h
        simp only [Fin.val_castAdd] at hv
        have hi := i.isLt; omega
      have he : Fin.castAdd 24 i=Fin.castAdd 1 (Fin.castAdd 6 (Fin.castAdd 17 i)) := Fin.ext rfl
      simp only [Function.update_of_ne hn,Fin.addCases_left]
      rw [he]
      simp only [Alphabet.mapTapes,AllAxisPolynomialPlacement.input,AllAxisPolynomialStreamInit.input,
        AllAxisFullStreamInit.input,AllAxisPhaseStreamInit.input,AllAxisAddressHeaders.initial,
        AllAxisPhaseHeadersData.initial,Tapes.append,Fin.addCases_left]
      exact (congrFun (congrArg Tapes.tape hb) i).symm
    | right i =>
      fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.AllAxisPhasePreparedBridge
