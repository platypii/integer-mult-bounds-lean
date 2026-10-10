import IntegerMultBounds.Machine.CompactNativeRoleSourceRuns

/-! Reassociate the physically copied fresh28 headers with fifteen blank
arithmetic tapes. This pays the producer lifecycle and exposes the exact43
numeric bank consumed by native role placement, without any payload move. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleScalarCaller
noncomputable section
open ActiveRepairRankHeadersCommands (bank)
variable {t u a : ℕ}

def association (t : ℕ) : Fin ((t+28)+15) ≃ Fin (t+43) := finCongr (by omega)

theorem associate (x : Tapes t a) (y : Tapes 28 a) (z : Tapes 15 a) :
    ((x.append y).append z).reindex (association t)=x.append (y.append z) := by
  have point (i : Fin (t+43)) :
      (((x.append y).append z).reindex (association t)).head i=(x.append (y.append z)).head i ∧
      (((x.append y).append z).reindex (association t)).tape i=(x.append (y.append z)).tape i := by
    induction i using Fin.addCases (m:=t) (n:=43) with
    | left i =>
      have he : (association t).symm (Fin.castAdd 43 i)=Fin.castAdd 15 (Fin.castAdd 28 i) := Fin.ext rfl
      simp only [Tapes.reindex,he,Tapes.append,Fin.addCases_left]
      trivial
    | right i =>
      induction i using Fin.addCases (m:=28) (n:=15) with
      | left i =>
        have he : (association t).symm (Fin.natAdd t (Fin.castAdd 15 i))=Fin.castAdd 15 (Fin.natAdd t i) := Fin.ext rfl
        simp only [Tapes.reindex,he,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        trivial
      | right i =>
        have he : (association t).symm (Fin.natAdd t (Fin.natAdd 28 i))=Fin.natAdd (t+28) i := by apply Fin.ext; dsimp [association]; omega
        simp only [Tapes.reindex,he,Tapes.append,Fin.addCases_right]
        trivial
  apply congrArg₂ Tapes.mk <;> funext i
  · exact (point i).1
  · exact (point i).2

theorem empty43 : (SharedBank.empty 28 a).append (SharedBank.empty 15 a)=SharedBank.empty 43 a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases (m:=28) (n:=15) <;> simp [SharedBank.empty]

def program (c m u : ℕ) :=
  reindex (extend (CompactNativeRoleScalarProducer.program c m u) 15) (association (43+(u+6)))

theorem runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hG : 0<G) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) (hDp : 0<D)
    (ctrl : Fin 6 → ℕ) (payload : Tapes u 2) :
    HoareTime (program c m u)
      (fun v => v=((bank (CompactReservedHeaders.initial D K rho ell q d G)).append
        (payload.append (CompactNativeRoleScalarProducer.controller ctrl))).append (SharedBank.empty 43 2))
      (fun v => v=((bank (CompactReservedHeaders.initial D K rho ell q d G)).append
        (payload.append (CompactNativeRoleScalarProducer.controller ctrl))).append
          (bank (CompactNativeRoleScalarProducer.outputState c m D K rho ell q d G ctrl)))
      (CompactNativeRoleScalarProducer.cost c m D K rho ell q d G u ctrl) := by
  have hh := hoare_reindex_eq (hoare_extend_eq
    (CompactNativeRoleScalarProducer.runs c m D K rho ell q d G hc hm hd hG hK hD hDp ctrl payload)
    (SharedBank.empty 15 2)) (association (43+(u+6)))
  simpa only [program,associate,empty43,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank] using hh

end
end IntegerMultBounds.Machine.CompactNativeRoleScalarCaller
