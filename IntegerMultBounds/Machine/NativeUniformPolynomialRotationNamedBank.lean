import IntegerMultBounds.Machine.NativeUniformPolynomialRotationNamedRoles
import IntegerMultBounds.Machine.NativeEndpointCharacterNamedBank

/-! Uniform corrections return the literal canonical native role bank. -/
namespace IntegerMultBounds.Machine.NativeUniformPolynomialRotationNamedBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRolePhaseSite (roleCount)
open CompactComplexEndpointRoleExchange (Address Wire tapes port)
open NativeUniformPolynomialRotationNamedRoles (source selected output)
variable {s u : ℕ} {sh : Shape} {rows ell : ℕ}

 def data (negative : Bool) (v : Stage sh) (before : Wire → Array sh rows ell) :
    Wire → Array sh rows ell := fun a => match negative,a with
  | true,Sum.inl b => UnitPhasePolynomialArray.result
      (NativeUniformPolynomialRotationOriginal.exponent true v) (before (Sum.inl b))
  | false,Sum.inr (Sum.inl b) => UnitPhasePolynomialArray.result
      (NativeUniformPolynomialRotationOriginal.exponent false v) (before (Sum.inr (Sum.inl b)))
  | _,a => before a

 theorem data_selected (negative : Bool) (v : Stage sh)
    (before : Wire → Array sh rows ell) (b : Address) :
    data negative v before (selected negative b)=UnitPhasePolynomialArray.result
      (NativeUniformPolynomialRotationOriginal.exponent negative v) (before (selected negative b)) := by
  cases negative <;> rfl

 theorem data_frame (negative : Bool) (v : Stage sh)
    (before : Wire → Array sh rows ell) (a : Wire) (ha : ¬∃ b,a=selected negative b) :
    data negative v before a=before a := by
  cases negative
  · rcases a with a | a | a
    · rfl
    · exact (ha ⟨a,rfl⟩).elim
    · rfl
  · rcases a with a | a | a
    · exact (ha ⟨a,rfl⟩).elim
    · rfl
    · rfl

 theorem source_selected (negative : Bool) (b : Address) :
    source (s:=s) (u:=u) negative b=port (selected negative b) := by
  cases negative <;> rfl

 theorem result_word (q : Fin 4) (xs : Array sh rows ell) :
    NativeZeroPaddingArray.word (UnitPhasePolynomialArray.result q xs)=
      UnitPhaseFullStreamNormalized.serialized (UnitPhasePolynomialArray.result q xs) := rfl
 theorem endpoint (negative : Bool) (v : Stage sh) (parentRows ell : ℕ)
    (before : Wire → Array sh (parentRows/roleCount) ell) (caller : Tapes (tapes s u) 2)
    (hh : ∀ a,caller.head (port a)=0)
    (hs : ∀ a,caller.tape (port a)=NativeZeroPadding.word (NativeZeroPaddingArray.word (before a))) :
    output negative v parentRows ell before caller=
      CompactComplexEndpointRoleExchange.bank caller (data negative v before) := by
  apply congrArg₂ Tapes.mk
  · funext i
    classical
    by_cases hi : ∃ a,port a=i
    · obtain ⟨a,rfl⟩ := hi
      by_cases ha : ∃ b,a=selected negative b
      · obtain ⟨b,rfl⟩ := ha
        have he := (NativeUniformPolynomialRotationNamedRoles.output_role negative v parentRows ell before caller b).1
        rw [source_selected] at he
        exact he.trans (hh (selected negative b)).symm
      · exact (NativeUniformPolynomialRotationNamedRoles.output_frame negative v parentRows ell before caller (port a)
          (by intro b h; rw [source_selected] at h; exact ha ⟨b,(CompactComplexEndpointRoleExchange.port_injective h).symm⟩)).1
    · exact (NativeUniformPolynomialRotationNamedRoles.output_frame negative v parentRows ell before caller i
        (by intro b h;rw [source_selected] at h;exact hi ⟨selected negative b,h⟩)).1
  · funext i
    classical
    change (output negative v parentRows ell before caller).tape i=
      (NamedRoleWordExchange.bank port caller (data negative v before)).tape i
    by_cases hi : ∃ a,port a=i
    · obtain ⟨a,rfl⟩ := hi
      by_cases ha : ∃ b,a=selected negative b
      · obtain ⟨b,rfl⟩ := ha
        have he := (NativeUniformPolynomialRotationNamedRoles.output_role negative v parentRows ell before caller b).2
        simpa only [NamedRoleWordExchange.bank_role port CompactComplexEndpointRoleExchange.port_injective,
          data_selected,NativeZeroPadding.word,result_word,source_selected] using he
      · have he := (NativeUniformPolynomialRotationNamedRoles.output_frame negative v parentRows ell before caller (port a)
          (by intro b h; rw [source_selected] at h; exact ha ⟨b,(CompactComplexEndpointRoleExchange.port_injective h).symm⟩)).2
        exact he.trans ((hs a).trans (by
          simp only [NamedRoleWordExchange.bank_role port CompactComplexEndpointRoleExchange.port_injective,
            data_frame negative v before a ha]))
    · have hn : ∀ a,port a≠i := by intro a h;exact hi ⟨a,h⟩
      have he := (NativeUniformPolynomialRotationNamedRoles.output_frame negative v parentRows ell before caller i
        (by intro b; rw [source_selected]; exact hn (selected negative b))).2
      exact he.trans (NamedRoleWordExchange.bank_frame port caller _ i hn).symm

 theorem caller_endpoint (negative : Bool) (v : Stage sh) (parentRows ell : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    (before : Wire → Array sh (parentRows/roleCount) ell) :
    output negative v parentRows ell before
      ((CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload master masterHead before)).append extra)=
      (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload master masterHead
          (data negative v before))).append extra := by
  rw [endpoint negative v parentRows ell before _
    (fun a => (CompactComplexEndpointRoleExchange.caller_roles control queue scalar stage tail storage
      extra master masterHead before a).1)
    (fun a => (CompactComplexEndpointRoleExchange.caller_roles control queue scalar stage tail storage
      extra master masterHead before a).2)]
  exact NativeEndpointCharacterNamedBank.caller_replace control queue scalar stage tail storage
    extra master masterHead _ _

end
end IntegerMultBounds.Machine.NativeUniformPolynomialRotationNamedBank
