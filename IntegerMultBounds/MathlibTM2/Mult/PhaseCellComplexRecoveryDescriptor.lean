module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareComplexRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSerializeOwnedDescriptorBank
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Ordinary complex payloads physically produce one raw-recovery descriptor.
The placed producer bank is erased, while descriptor suffix and clock survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

def complexRecoveryDescriptor (work : Fin 392 → Fin T) (dst tmp saved clock : Fin T) : Pr P T Q A U :=
  .seq (embProg work Empty.elim prepareComplexRecoveryInput)
    (serializeOwnedDescriptorBank work dst tmp saved clock)

omit [NeZero s] in
theorem complexRecoveryDescriptor_pushBound (work : Fin 392 → Fin T) (dst tmp saved clock : Fin T) :
    mnNativePushBound 2 (complexRecoveryDescriptor (P := P) (Q := Q) (A := A) (U := U)
      work dst tmp saved clock) := by
  exact ⟨embProg_native _ Empty.elim _ prepareComplexRecoveryInput_pushBound,
    serializeOwnedDescriptorBank_pushBound _ _ _ _ _⟩

theorem complexRecoveryDescriptor_exec (hA : 4 ≤ A) (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (hN : H.Fs.length = 2*Fs.length)
    (work : Fin 392 → Fin T) (hwork : Function.Injective work)
    (dst tmp saved clock : Fin T) (hreg : [dst,tmp,saved,clock].Nodup)
    (hsep : ∀ i, work i ∉ [dst,tmp,saved,clock])
    (v : HS T Q A U) (S : Stacks T A)
    (hinput : embStk work S = complexRecoveryInput H W Fs S.inp S.out)
    (htmp : S.R tmp = []) (hsaved : S.R saved = []) :
    let words := (rawRecoveryInput (A := A) H W (complexComponentFields Fs) [] []).R
    let tape := descriptorBankTape (placedDescriptorFields work words)
    let budget := prepareComplexRecoveryInputCost H.span W Fs.length+13*tape.length+3
    ∃ v' steps, v'.user = v.user ∧ steps ≤ budget ∧
      Exec body (complexRecoveryDescriptor work dst tmp saved clock) (mk v S) steps
        (mk v' (serializedOwnedDescriptorState work dst clock tape S)) ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*budget) depth
        (complexRecoveryDescriptor work dst tmp saved clock) (mk v S) steps
        (mk v' (serializedOwnedDescriptorState work dst clock tape S)) := by
  dsimp only
  let F := rawRecoveryInput (A := A) H W (complexComponentFields Fs) S.inp S.out
  let words := (rawRecoveryInput (A := A) H W (complexComponentFields Fs) [] []).R
  let tape := descriptorBankTape (placedDescriptorFields work words)
  obtain ⟨vf,n₁,hu₁,hn₁,he₁⟩ := prepareComplexRecoveryInput_exec hA H W Fs hN S.inp S.out (embDn work v)
  obtain ⟨v₁,_,hu₁',he₁'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    hwork (fun f => nomatch f) he₁ v rfl S hinput
  let M := embOvr work F.get S
  have hwords (i : Fin 392) : M.R (work i) = words i := by
    change embExt work F.R S.R (work i) = words i
    rw [embExt_apply hwork]
    rfl
  have hoff (k : Fin T) (hk : ∀ i, work i ≠ k) : M.R k = S.R k :=
    (embOvr_off (e := work) F.get S hk).2
  have hports (i : Fin 392) : work i ≠ dst ∧ work i ≠ tmp ∧ work i ≠ saved ∧ work i ≠ clock := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hsep i
  have hdst : M.R dst = S.R dst := hoff _ (fun i => (hports i).1)
  have hclock : M.R clock = S.R clock := hoff _ (fun i => (hports i).2.2.2)
  have hML : M.L = S.L := by
    change embExt work (fun _ => []) S.L = S.L
    have hleft : (fun _ : Fin 392 => ([] : List (Fin (A+4)))) = S.L ∘ work := by
      funext i
      have hh := congrArg (fun B : Stacks 392 A => B.L i) hinput
      exact hh.symm
    rw [hleft,embExt_comp]
  have htape : descriptorBankTape ((List.ofFn work).map (fun k => (k,M.R k))) = tape :=
    descriptorBankTape_sources_eq work work words M.R hwords
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂,_⟩ := serializeOwnedDescriptorBank_exec (body := body) work hwork
    dst tmp saved clock hreg hsep v₁ M
    (by rw [hoff _ (fun i => (hports i).2.1)]; exact htmp)
    (by rw [hoff _ (fun i => (hports i).2.2.1)]; exact hsaved)
  rw [htape] at hn₂ he₂
  have hcleared : (fun k => if k ∈ List.ofFn work then [] else M.R k) =
      (fun k => if k ∈ List.ofFn work then [] else S.R k) := by
    funext k
    split_ifs with hk
    · rfl
    · exact hoff k (by intro i he; exact hk (List.mem_ofFn.mpr ⟨i,he⟩))
  have hfinal : serializedOwnedDescriptorState work dst clock tape M =
      serializedOwnedDescriptorState work dst clock tape S := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · exact hML
    dsimp only [serializedOwnedDescriptorState]
    rw [hcleared,hdst,hclock]
  rw [hfinal] at he₂
  have he : Exec body (complexRecoveryDescriptor work dst tmp saved clock) (mk v S) (n₁+n₂)
      (mk v₂ (serializedOwnedDescriptorState work dst clock tape S)) := Exec.seq he₁' he₂
  have hn : n₁+n₂ ≤ prepareComplexRecoveryInputCost H.span W Fs.length+13*tape.length+3 := by omega
  exact ⟨v₂,n₁+n₂,hu₂.trans (hu₁'.trans hu₁),hn,he,fun depth =>
    mn_native_exec_within he 2 (complexRecoveryDescriptor_pushBound _ _ _ _ _) depth _ (by
      dsimp only [tape,words] at hn
      omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
