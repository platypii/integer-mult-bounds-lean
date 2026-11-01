module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareComplexRecoveryInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedHeaderCopies

/-! The sparse ordinary header interface for complex recovery input. Only live
unary metadata is copied; the exposed complex payload has its own register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def complexRecoveryHeaderPorts : List (Fin 392) :=
  [94,97,98,99,100,101,108,111,112,113,114,115,121,123,129,130,138,390]

noncomputable def complexRecoveryHeader {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (W N : ℕ) (k : Fin 392) : ℕ :=
  if k = 138 then H.span else if k = 390 then N else
  if k = 130 then W else if k = 129 then H.p else
  if hk : k.val < 126 then generatedRecoveryHeader H ⟨k.val,hk⟩ else 0

theorem complexRecoveryHeader_off {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (W N : ℕ) (k : Fin 392) (hk : k ∉ complexRecoveryHeaderPorts) :
    complexRecoveryHeader H W N k = 0 := by
  simp only [complexRecoveryHeaderPorts,List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff] at hk
  by_cases hlow : k.val < 126
  all_goals simp_all [complexRecoveryHeader,generatedRecoveryHeader,replicaFactoryHeaderValue,Fin.ext_iff]

theorem complexRecoveryInput_right {s A : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (W : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (inp : List (Bool ⊕ Bool)) (out : List Bool) (k : Fin 392) :
    (complexRecoveryInput (A := A) H W Fs inp out).R k =
      if k = 124 then cstream A W (Fs.map (packedInterval H.origin H.span)).flatten
      else List.replicate (complexRecoveryHeader H W Fs.length k) tick := by
  by_cases h138 : k = 138
  · subst k; simp [complexRecoveryInput,complexRecoveryHeader]
  by_cases h390 : k = 390
  · subst k; simp [complexRecoveryInput,complexRecoveryHeader]
  by_cases h130 : k = 130
  · subst k; simp [complexRecoveryInput,rawRecoveryInput,complexRecoveryHeader]
  by_cases h129 : k = 129
  · subst k; simp [complexRecoveryInput,rawRecoveryInput,complexRecoveryHeader]
  by_cases h124 : k = 124
  · subst k; simp [complexRecoveryInput,rawRecoveryInput]
  simp only [complexRecoveryInput,rawRecoveryInput,generatedRecoveryInput,complexRecoveryHeader,
    Function.update_of_ne h138,Function.update_of_ne h390,Function.update_of_ne h130,
    Function.update_of_ne h129,Function.update_of_ne h124,h138,h390,h130,h129,h124,ite_false]
  split_ifs <;> rfl


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
