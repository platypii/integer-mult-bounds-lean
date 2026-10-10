import IntegerMultBounds.Machine.NativeEndpointCharacterNamedRoles

/-! The physical role loop returns the literal named bank, with only its
original source/sink character family changed. All permanent caller frames
are recovered without assuming a local endpoint equation. -/
namespace IntegerMultBounds.Machine.NativeEndpointCharacterNamedBank
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters (Stage)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexEndpointRoleExchange (Address Wire tapes port)
open NativeEndpointCharacterNamedRoles (role source coefficients output)
open NativeEndpointCharacterRoles (arity)
open CompactComplexRolePhaseSite (roleCount roleEncoding)
variable {s u : ℕ} {sh : Shape} {rows ell : ℕ}

 def result (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    {rows : ℕ} (data : Wire → Array sh rows ell) (b : Address) : Array sh rows ell :=
  fun i => AllAxisPolynomialLiteralEndpoint.result (N:=rows*2^sh.bits) (R:=2^ell)
    (NativePolynomialStageShape.stage v ell p) arity
    (NativeEndpointCharacterTerminal.terminalWeights v hslots b) (coefficients data (role sink b))
    (Fin.cast (Nat.mul_assoc rows (2^sh.bits) (2^ell)).symm i)

 def data (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    {rows : ℕ} (before : Wire → Array sh rows ell) : Wire → Array sh rows ell :=
  fun a => match sink,a with
    | false,Sum.inl b => result false v hslots ell p before b
    | true,Sum.inr (Sum.inl b) => result true v hslots ell p before b
    | _,a => before a

 theorem data_selected (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (before : Wire → Array sh rows ell) (b : Address) :
    data sink v hslots ell p before (role sink b)=result sink v hslots ell p before b := by
  cases sink <;> rfl

 theorem data_frame (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (before : Wire → Array sh rows ell) (a : Wire) (ha : ¬∃ b,a=role sink b) :
    data sink v hslots ell p before a=before a := by
  cases sink
  · rcases a with a | a | a
    · exact (ha ⟨a,rfl⟩).elim
    · rfl
    · rfl
  · rcases a with a | a | a
    · rfl
    · exact (ha ⟨a,rfl⟩).elim
    · rfl

 theorem result_word (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (before : Wire → Array sh rows ell) (b : Address) :
    NativeZeroPaddingArray.word (result sink v hslots ell p before b)=
      UnitPhaseFullStreamNormalized.serialized
        (AllAxisPolynomialLiteralEndpoint.result (N:=rows*2^sh.bits) (R:=2^ell)
          (NativePolynomialStageShape.stage v ell p) arity
          (NativeEndpointCharacterTerminal.terminalWeights v hslots b) (coefficients before (role sink b))) := by
  unfold NativeZeroPaddingArray.word UnitPhaseFullStreamNormalized.serialized result
  congr 1
  exact (List.ofFn_congr (Nat.mul_assoc rows (2^sh.bits) (2^ell))
    (fun i => ButterflyStreamData.encoded
      (AllAxisPolynomialLiteralEndpoint.result (N:=rows*2^sh.bits) (R:=2^ell)
        (NativePolynomialStageShape.stage v ell p) arity
        (NativeEndpointCharacterTerminal.terminalWeights v hslots b) (coefficients before (role sink b)) i))).symm

 theorem endpoint (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (before : Wire → Array sh rows ell) (caller : Tapes (tapes s u) 2)
    (hh : ∀ a,caller.head (port a)=0)
    (hs : ∀ a,caller.tape (port a)=NativeZeroPadding.word (NativeZeroPaddingArray.word (before a))) :
    output sink v ell p before caller=
      CompactComplexEndpointRoleExchange.bank caller (data sink v hslots ell p before) := by
  apply congrArg₂ Tapes.mk
  · funext i
    classical
    by_cases hi : ∃ a,port a=i
    · obtain ⟨a,rfl⟩ := hi
      by_cases ha : ∃ b,a=role sink b
      · obtain ⟨b,rfl⟩ := ha
        exact (NativeEndpointCharacterNamedRoles.endpoint_role sink v hslots ell p before caller b).1.trans
          (hh (role sink b)).symm
      · exact (NativeEndpointCharacterNamedRoles.endpoint_frame sink v ell p before caller (port a)
          (by intro b h; exact ha ⟨b,(CompactComplexEndpointRoleExchange.port_injective h).symm⟩)).1
    · exact (NativeEndpointCharacterNamedRoles.endpoint_frame sink v ell p before caller i
        (by intro b h;exact hi ⟨role sink b,h⟩)).1
  · funext i
    classical
    change (output sink v ell p before caller).tape i=
      (NamedRoleWordExchange.bank port caller (data sink v hslots ell p before)).tape i
    by_cases hi : ∃ a,port a=i
    · obtain ⟨a,rfl⟩ := hi
      by_cases ha : ∃ b,a=role sink b
      · obtain ⟨b,rfl⟩ := ha
        have he := (NativeEndpointCharacterNamedRoles.endpoint_role sink v hslots ell p before caller b).2
        simpa only [NamedRoleWordExchange.bank_role port CompactComplexEndpointRoleExchange.port_injective,
          data_selected,NativeZeroPadding.word,result_word,source] using he
      · have he := (NativeEndpointCharacterNamedRoles.endpoint_frame sink v ell p before caller (port a)
          (by intro b h; exact ha ⟨b,(CompactComplexEndpointRoleExchange.port_injective h).symm⟩)).2
        exact he.trans ((hs a).trans (by
          simp only [NamedRoleWordExchange.bank_role port CompactComplexEndpointRoleExchange.port_injective,
            data_frame sink v hslots ell p before a ha]))
    · have hn : ∀ a,port a≠i := by intro a h;exact hi ⟨a,h⟩
      have he := (NativeEndpointCharacterNamedRoles.endpoint_frame sink v ell p before caller i
        (fun b => hn (role sink b))).2
      exact he.trans (NamedRoleWordExchange.bank_frame port caller _ i hn).symm

private def words {A S : Type*} {c : ℕ} (e : NamedRoleWordExchange.Role A S ≃ Fin c)
    {sh : Shape} {rows ell : ℕ} (data : NamedRoleWordExchange.Role A S → Array sh rows ell) : Tapes c 2 :=
  ⟨fun _ => 0,fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (data (e.symm j)))⟩

/-- Abstract counts keep this identity independent of the astronomical
original role cardinality. -/
private theorem replace_roles {A S : Type*} {n c u : ℕ}
    (e : NamedRoleWordExchange.Role A S ≃ Fin c)
    (base : Tapes n 2) (extra : Tapes u 2) {sh : Shape} {rows ell : ℕ}
    (before after : NamedRoleWordExchange.Role A S → Array sh rows ell) :
    NamedRoleWordExchange.bank (fun a => Fin.castAdd u (Fin.natAdd n (e a)))
      ((base.append (words e before)).append extra) after=
      (base.append (words e after)).append extra := by
  have hinj : Function.Injective (fun a => Fin.castAdd u (Fin.natAdd n (e a))) := by
    intro a b h
    have hv := congrArg (fun j : Fin ((n+c)+u) => j.val) h
    apply e.injective
    apply Fin.ext
    simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  apply congrArg₂ Tapes.mk
  · funext i
    induction i using Fin.addCases (m:=n+c) (n:=u) with
    | right i => simp only [Tapes.append,Fin.addCases_right]
    | left i =>
      induction i using Fin.addCases (m:=n) (n:=c) with
      | left i => simp only [Tapes.append,Fin.addCases_left]
      | right i => simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,words]
  · funext i
    change (NamedRoleWordExchange.bank (fun a => Fin.castAdd u (Fin.natAdd n (e a)))
      ((base.append (words e before)).append extra) after).tape i=
      ((base.append (words e after)).append extra).tape i
    induction i using Fin.addCases (m:=n+c) (n:=u) with
    | right i =>
      rw [NamedRoleWordExchange.bank_frame]
      · simp only [Tapes.append,Fin.addCases_right]
      · intro a h
        have hv := congrArg (fun j : Fin ((n+c)+u) => j.val) h
        have ha := (e a).isLt
        simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
        omega
    | left i =>
      induction i using Fin.addCases (m:=n) (n:=c) with
      | left i =>
        rw [NamedRoleWordExchange.bank_frame]
        · simp only [Tapes.append,Fin.addCases_left]
        · intro a h
          have hv := congrArg (fun j : Fin ((n+c)+u) => j.val) h
          have hi := i.isLt
          simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
          omega
      | right i =>
        have he : Fin.castAdd u (Fin.natAdd n i)=Fin.castAdd u (Fin.natAdd n (e (e.symm i))) := by
          rw [Equiv.apply_symm_apply]
        rw [he,NamedRoleWordExchange.bank_role _ hinj]
        simp only [Tapes.append,Fin.addCases_left,Fin.addCases_right,words,Equiv.apply_symm_apply]

private theorem role_payload (source : ℤ → Fin 6) (sourceHead : ℤ)
    {sh : Shape} {rows ell : ℕ} (data : Wire → Array sh rows ell) :
    CompactNativeRoleSourcePorts.roles (CompactComplexEndpointRoleExchange.payload source sourceHead data)=
      words roleEncoding data := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    have he : (⟨i.val+1,by omega⟩ : Fin (1+roleCount))=Fin.natAdd 1 i := Fin.ext (by simp;omega)
    simp only [CompactComplexEndpointRoleExchange.payload,
      CyclicRowCopy.payload,he,Tapes.append,Fin.addCases_right]


/-- Replacing the original named words reconstructs the whole original caller
with the changed role payload and identical controller, geometry and suffix. -/
theorem caller_replace (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    {rows ell : ℕ} (before after : Wire → Array sh rows ell) :
    CompactComplexEndpointRoleExchange.bank
      ((CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload master masterHead before)).append extra) after=
      (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload master masterHead after)).append extra := by
  unfold CompactComplexEndpointRoleExchange.bank CompactComplexNativeCodecFrame.bank
    CompactComplexNativeRoleBridge.bank
  rw [role_payload,role_payload]
  exact replace_roles roleEncoding _ _ before after

/-- The complete output of the actual character loop is a canonical bank with
its changed role payload; every controller and external suffix is literal. -/
theorem caller_endpoint (sink : Bool) (v : Stage sh) (hslots : v.slots=arity) (ell p : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2)
    (scalar stage : ActiveRepairRankHeadersCommands.State) (tail : Tapes 22 2)
    (storage : Tapes s 2) (extra : Tapes u 2) (master : ℤ → Fin 6) (masterHead : ℤ)
    {rows : ℕ} (before : Wire → Array sh rows ell) :
    output sink v ell p before
      ((CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload master masterHead before)).append extra)=
      (CompactComplexNativeCodecFrame.bank control queue scalar stage tail storage
        (CompactComplexEndpointRoleExchange.payload master masterHead
          (data sink v hslots ell p before))).append extra := by
  rw [endpoint sink v hslots ell p before _
    (fun a => (CompactComplexEndpointRoleExchange.caller_roles control queue scalar stage tail storage
      extra master masterHead before a).1)
    (fun a => (CompactComplexEndpointRoleExchange.caller_roles control queue scalar stage tail storage
      extra master masterHead before a).2)]
  exact caller_replace control queue scalar stage tail storage extra master masterHead _ _

end
end IntegerMultBounds.Machine.NativeEndpointCharacterNamedBank
