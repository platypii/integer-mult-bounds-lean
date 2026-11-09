module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalNormalizedCorePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPackedNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies

/-! Ordinary width and crop headers initialize the numerical core's added
workspace. A named entry state hides the historical chain of extensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicComplexCoreInput (S : Stacks 834 A) (wide radius core : List (Fin (A+4))) : Stacks 909 A :=
  let E := extendStacks (by decide : 834 ≤ 909) S
  {E with R := (Function.update (Function.update (Function.update E.R 906 wide) 907 radius) 908 core)}

theorem cyclicComplexCoreInput_eq (S : Stacks 834 A) (wide radius core : List (Fin (A+4))) :
    cyclicComplexCoreInput S wide radius core =
      normalizedCorePublicationInput (cyclicPackedNormalizationInput
        (extendStacks (by decide : 842 ≤ 850) (extendStacks (by decide : 840 ≤ 842)
          (extendStacks (by decide : 834 ≤ 840) S))) wide) radius core := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    simp only [cyclicComplexCoreInput,normalizedCorePublicationInput,cyclicPackedNormalizationInput,
      extendStacks,Fin.val_mk]
    split_ifs <;> first | rfl | (simp_all [Fin.ext_iff] <;> omega)
  · funext i
    simp only [cyclicComplexCoreInput,normalizedCorePublicationInput,cyclicPackedNormalizationInput,
      extendStacks,Function.update_apply,Fin.val_mk]
    split_ifs <;> first | rfl | (simp_all [Fin.ext_iff] <;> omega)

def cyclicComplexControlPort : Fin 3 → Fin 909 := ![906,907,908]

def cyclicComplexControlCopies (bank : Fin 909 → Fin T) (source : Fin 3 → Fin T) : List (Fin T × Fin T) :=
  List.ofFn (fun i => (source i,bank (cyclicComplexControlPort i)))

theorem cyclicComplexControlCopies_cost (bank : Fin 909 → Fin T) (source : Fin 3 → Fin T)
    (W radius core : ℕ) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![W,radius,core] i) :
    copyUnaryHeadersCost (fun k => (S.R k).length) (cyclicComplexControlCopies bank source) =
      4*(W+radius+core)+13 := by
  simp [copyUnaryHeadersCost,cyclicComplexControlCopies,List.ofFn_succ,hvalues]
  omega

def installCyclicComplexCoreControls (bank : Fin 909 → Fin T) (source : Fin 3 → Fin T) (tmp : Fin T) : Pr P T Q A U :=
  copyUnaryHeaders tmp (cyclicComplexControlCopies bank source)

theorem installCyclicComplexCoreControls_exec (bank : Fin 909 → Fin T) (hbank : Function.Injective bank)
    (source : Fin 3 → Fin T) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ bank j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hbankTmp : ∀ i, bank i ≠ tmp) (W radius core : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![W,radius,core] i)
    (hfresh : ∀ i : Fin 909, 834 ≤ i.val → S.L (bank i) = [] ∧ S.R (bank i) = [])
    (htmp : S.R tmp = []) :
    let rs := cyclicComplexControlCopies bank source
    let cost := copyUnaryHeadersCost (fun k => (S.R k).length) rs
    ∃ v' G, v'.user = v.user ∧
      Exec body (installCyclicComplexCoreControls bank source tmp) (mk v S) cost (mk v' G) ∧
      embStk bank G = cyclicComplexCoreInput
        (embStk (bank ∘ Fin.castLE (by decide : 834 ≤ 909)) S)
        (List.replicate W tick) (List.replicate radius tick) (List.replicate core tick) ∧
      G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, (∀ i, bank i ≠ k) → G.R k = S.R k) := by
  dsimp only
  let rs := cyclicComplexControlCopies bank source
  let value := fun k => (S.R k).length
  let G : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  obtain ⟨v',hu,hex⟩ := copyUnaryHeaders_exec (body := body) tmp rs
    (by
      intro r hr
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨⟨hsourceOff i _,hsourceTmp i⟩,hbankTmp _,⟨not_false,List.nodup_nil⟩⟩)
    (by
      intro r hr q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
      exact (hsourceOff j _).symm) value v S (fun _ _ => rfl) htmp
  have hnd : (rs.map Prod.snd).Nodup := by
    simp only [rs,cyclicComplexControlCopies,List.map_ofFn,Function.comp_def]
    apply List.nodup_ofFn_ofInjective
    apply hbank.comp
    decide +kernel
  have hport (i : Fin 3) : G.R (bank (cyclicComplexControlPort i)) =
      List.replicate (![W,radius,core] i) tick := by
    have hh := unaryCopiesR_at value S.R rs hnd _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    change unaryCopiesR value S.R rs _ = _
    rw [hh,(hfresh _ (by fin_cases i <;> decide)).2,List.append_nil]
    simp only [value,hvalues]
  have hoff (i : Fin 909) (hi : ∀ j, cyclicComplexControlPort j ≠ i) : G.R (bank i) = S.R (bank i) := by
    apply unaryCopiesR_off
    intro r hr he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi j (hbank he)
  refine ⟨v',G,hu,hex,?_,rfl,rfl,rfl,?_⟩
  · refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      by_cases hi : i.val < 834
      · simp [embStk,cyclicComplexCoreInput,extendStacks,hi,G]
      · simpa [embStk,cyclicComplexCoreInput,extendStacks,hi,G] using (hfresh i (by omega)).1
    · funext i
      by_cases h906 : i = 906
      · subst i; simpa [cyclicComplexCoreInput,embStk_R,cyclicComplexControlPort] using hport 0
      by_cases h907 : i = 907
      · subst i; simpa [cyclicComplexCoreInput,embStk_R,cyclicComplexControlPort] using hport 1
      by_cases h908 : i = 908
      · subst i; simpa [cyclicComplexCoreInput,embStk_R,cyclicComplexControlPort] using hport 2
      have hh := hoff i (by
        intro j
        fin_cases j
        · exact Ne.symm h906
        · exact Ne.symm h907
        · exact Ne.symm h908)
      by_cases hi : i.val < 834
      · simpa [embStk,cyclicComplexCoreInput,extendStacks,hi,h906,h907,h908] using hh
      · simpa [embStk,cyclicComplexCoreInput,extendStacks,hi,h906,h907,h908] using hh.trans (hfresh i (by omega)).2
  · intro k hk
    apply unaryCopiesR_off
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact hk _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
