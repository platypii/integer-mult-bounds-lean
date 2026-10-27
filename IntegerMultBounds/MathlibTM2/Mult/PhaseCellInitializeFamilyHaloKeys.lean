module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloWeightFamily
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeLengthKeysReady

/-! Install the generated runtime key schedule below the retained weight family. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def initializeFamilyHaloKeys : Pr P₀ 151 Q A U :=
  embProg weightFamilyLegacyReg Empty.elim (initializeHaloLengthKeys (P₀ := Empty))

def initializedFamilyKeyR {A : ℕ} (R : Regs 151 A) (V w K : ℕ) (keys : List (Fin (A+4))) : Regs 151 A :=
  Function.update (Function.update (Function.update (Function.update R
    125 (List.replicate V tick)) 126 (keys++R 126)) 127 (List.replicate K tick)) 130 (List.replicate w tick)

theorem initializedFamilyKeyR_legacy {A : ℕ} (S : Stacks 151 A) (V w K : ℕ) (keys : List (Fin (A+4))) :
    weightFamilyLegacyBank {S with R := initializedFamilyKeyR S.R V w K keys} =
      {weightFamilyLegacyBank S with R := initializedKeyRuntimeR (weightFamilyLegacyBank S).R V w K keys} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [weightFamilyLegacyBank,initializedFamilyKeyR,initializedKeyRuntimeR,embStk,
    weightFamilyCoreReg,cachedGroupLegacyReg,Function.update_apply,Fin.ext_iff]

theorem LengthKeyReady.initialized_family {A P N q l s t u band V w K : ℕ}
    {raw : List (Fin (A+4))} {S : Stacks 151 A} (keys : List (Fin (A+4)))
    (h : LengthKeyReady P N q l s t u band 0 0 raw (weightFamilyLegacyBank S)) :
    LengthKeyReady P N q l s t u band V w raw
      (weightFamilyLegacyBank {S with R := initializedFamilyKeyR S.R V w K keys}) := by
  rw [initializedFamilyKeyR_legacy]
  exact h.initialized

theorem initializeFamilyHaloKeys_exec (P N q l s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 151 Q A U) (S : Stacks 151 A) (raw : List (Fin (A+4)))
    (hready : LengthKeyReady P N q l s t u band 0 0 raw (weightFamilyLegacyBank S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (h127 : S.R 127 = []) (h138 : S.R 138 = []) :
    let w := 2*q+8
    let V := weightWorkspaceWidth P q w t u
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeHaloLengthKeysCost P N q l s t u band a b ∧
      Exec body initializeFamilyHaloKeys (mk v S) n
        (mk v' {S with R := (initializedFamilyKeyR S.R V w (haloLengthKeys s t band a b).length
          (haloPositiveLengthPackets A V s t band a b))}) := by
  dsimp only
  let w := 2*q+8
  let V := weightWorkspaceWidth P q w t u
  let K := (haloLengthKeys s t band a b).length
  let keys := haloPositiveLengthPackets A V s t band a b
  have h125 : (weightFamilyLegacyBank S).R 125 = [] := List.eq_nil_of_length_eq_zero hready.keyWidth
  have h130 : (weightFamilyLegacyBank S).R 130 = [] := List.eq_nil_of_length_eq_zero hready.wordWidth
  obtain ⟨vi,n,hui,hn,hei⟩ := initializeHaloLengthKeys_exec (body := fun p : Empty => nomatch p)
    P N q l s t u band a b hP hs hst hu hband has hbs hA (embDn weightFamilyLegacyReg v)
    (weightFamilyLegacyBank S) hready.masters ha hb hready.left hready.blank (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      · exact h125
      · exact h127
      · exact h130
      · exact hready.headerTemp
      · exact h138)
  obtain ⟨v',hv,hu',he⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightFamilyLegacyReg_injective (fun p => nomatch p) hei v rfl S rfl
  refine ⟨v',n,hu'.trans hui,hn,he.cast rfl ?_⟩
  apply congrArg (mk v')
  change embOvr weightFamilyLegacyReg
    ({ { { {weightFamilyLegacyBank S with R := Function.update (weightFamilyLegacyBank S).R 125 (List.replicate V tick)}
      with R := Function.update (Function.update (weightFamilyLegacyBank S).R 125 (List.replicate V tick)) 126 (keys++S.R 126)}
      with R := Function.update (Function.update (Function.update (weightFamilyLegacyBank S).R 125 (List.replicate V tick)) 126 (keys++S.R 126)) 127 (List.replicate K tick)}
      with R := Function.update (Function.update (Function.update (Function.update (weightFamilyLegacyBank S).R 125 (List.replicate V tick)) 126 (keys++S.R 126)) 127 (List.replicate K tick)) 130 (List.replicate w tick)} : Stacks 144 A).get S = _
  have hbase : embOvr weightFamilyLegacyReg (weightFamilyLegacyBank S).get S = S := embOvr_stk S
  rw [embOvr_updR weightFamilyLegacyReg_injective,embOvr_updR weightFamilyLegacyReg_injective,
    embOvr_updR weightFamilyLegacyReg_injective,embOvr_updR weightFamilyLegacyReg_injective,hbase]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
