module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOuterHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyRuntimeFrame

/-! Generate the key schedule in the private bank while preserving the caller's
retained parameters, input, output and borrowed stacks. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def protectedPrepareHaloLengthKeys : Pr P₀ 144 Q A U :=
  embProg groupReg id prepareHaloLengthKeys

theorem protectedPrepareHaloLengthKeys_exec (P N q l s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 144 Q A U) (S : Stacks 144 A) (raw outTail : List (Fin (A+4)))
    (hbank : embStk groupReg S =
      haloGroupInputBank P N q l s t u band a b 0 raw [] outTail S.inp S.out) :
    let w := 2*q+8
    let V := weightWorkspaceWidth P q w t u
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloLengthKeysCost P q s t u band a b ∧
      Exec (embTab groupReg body) protectedPrepareHaloLengthKeys (mk v S) n
        (mk v' { S with R := (generatedKeyRuntimeR S.R V w
          (haloLengthKeys s t band a b).length (haloPositiveLengthPackets A V s t band a b)) }) := by
  dsimp only
  let small := haloGroupInputBank P N q l s t u band a b 0 raw [] outTail S.inp S.out
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := prepareHaloLengthKeys_exec (body := body)
    P q s t u band a b hP hs hst hu hband has hbs hA (embDn groupReg v) small
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
    (by
      intro k hk
      have hn (n : ℕ) (hn : 31 ≤ n) : k.val ≠ n := by omega
      simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank,Fin.ext_iff,hn 111 (by decide),hn 113 (by decide),hn 101 (by decide),hn 102 (by decide),
        hn 103 (by decide),hn 97 (by decide),hn 98 (by decide),hn 99 (by decide),
        hn 100 (by decide),hn 109 (by decide),hn 112 (by decide),hn 114 (by decide),
        hn 116 (by decide),hn 110 (by decide),hn 93 (by decide)]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals simp [small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank])
  have hbody : ∀ f, embTab groupReg body (id f) = embProg groupReg id (body f) := fun _ => rfl
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr groupReg_injective hbody he₁ v rfl S hbank
  have hbase : embOvr groupReg small.get S = S := by
    change embOvr groupReg (haloGroupInputBank P N q l s t u band a b 0 raw [] outTail S.inp S.out).get S = S
    rw [← hbank]
    exact embOvr_stk S
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  congr 1
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let S94 : Stacks 117 A := { small with R := Function.update small.R 94 (List.replicate w tick) }
  let S115 : Stacks 117 A := { S94 with R := Function.update S94.R 115 (List.replicate V tick) }
  let S87 : Stacks 117 A := { S115 with R := (Function.update S115.R 87
    (haloPositiveLengthPackets A V s t band a b++small.R 87)) }
  change embOvr groupReg ({ S87 with R := (Function.update S87.R 86
    (List.replicate (haloLengthKeys s t band a b).length tick)) } : Stacks 117 A).get S = _
  rw [embOvr_updR groupReg_injective]
  dsimp only [S87]
  rw [embOvr_updR groupReg_injective]
  dsimp only [S115]
  rw [embOvr_updR groupReg_injective]
  dsimp only [S94]
  rw [embOvr_updR groupReg_injective,hbase]
  simp [generatedKeyRuntimeR,small,haloGroupInputBank,haloEndpointR,naturalGroupInputBank,batchInputBank,groupReg,V,w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
