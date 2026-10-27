module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloWeightClass

/-! Decode a runtime length, generate its exact numerical packet, then release
its owned unary length. Only the key suffix and completed family change. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def generateHaloWeightLengthKey : Pr P₀ 151 Q A U :=
  .seq (takeUnaryKey 125 126 128 134 135 136 137) (.seq generateHaloWeightClass (uclear 128))

def generateHaloWeightLengthKeyCost (P N q l s t u band a b V L : ℕ) : ℕ :=
  (6*L+19*V+14)+generateHaloWeightClassCost P N q l s t u band a b L+(2*L+2)

theorem weightFamilyLegacyBank_key {A : ℕ} (S : Stacks 151 A) (tail length : List (Fin (A+4))) :
    weightFamilyLegacyBank {S with R := (Function.update (Function.update S.R 126 tail) 128 length)} =
      {weightFamilyLegacyBank S with R := (Function.update (Function.update (weightFamilyLegacyBank S).R 126 tail) 128 length)} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg,Function.update_apply,Fin.ext_iff]

theorem generateHaloWeightLengthKey_exec (P N q l s t u band a b V L : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A) (hkey : L < 2^V)
    (v : HS 151 Q A U) (S : Stacks 151 A) (tail : List (Fin (A+4)))
    (hV : (S.R 125).length = V) (hkeys : S.R 126 = binSyms V L++tail)
    (hmasters : ∀ r ∈ groupHeaderCopies, ((weightFamilyLegacyBank S).R r.1).length =
      groupHeaderValue P N q l s t u band 0 r.1)
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hleft : ∀ k : Fin 144, k.val < 117 → (weightFamilyLegacyBank S).L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → (weightFamilyLegacyBank S).R k = [])
    (h133 : S.R 133 = [])
    (hfresh : ∀ i ∈ ([(134 : Fin 151),135,136,137,144,145,146,147,149] : List (Fin 151)), S.R i = []) :
    let page := batchWeightPage A (2*q+8) q P s t u (haloLengthGroup s t band a b L).length L
      (fun n => (haloGroupOrigin s t band a b L n).val)
    ∃ v' m, v'.user = v.user ∧ m ≤ generateHaloWeightLengthKeyCost P N q l s t u band a b V L ∧
      Exec body generateHaloWeightLengthKey (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 126 tail) 150
          ((weightKeyPacket page).reverse++S.R 150))}) := by
  dsimp only
  let page := batchWeightPage A (2*q+8) q P s t u (haloLengthGroup s t band a b L).length L
    (fun n => (haloGroupOrigin s t band a b L n).val)
  have h128 : S.R 128 = [] := by
    have hh := hmasters (128,102) (by simp [groupHeaderCopies])
    have hz : (weightFamilyLegacyBank S).R 128 = [] := List.eq_nil_of_length_eq_zero (by simpa [groupHeaderValue] using hh)
    exact hz
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeUnaryKey_exec (body := body)
    (show [(125 : Fin 151),126,128,134,135,136,137].Nodup by decide) V L hkey tail v S hV hkeys (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl
      · exact h128
      all_goals exact hfresh _ (by simp))
  let T : Stacks 151 A := {S with R := (Function.update (Function.update S.R 126 tail) 128 (List.replicate L tick))}
  have hmastersT : ∀ r ∈ groupHeaderCopies, ((weightFamilyLegacyBank T).R r.1).length =
      groupHeaderValue P N q l s t u band L r.1 := by
    intro r hr
    change ((weightFamilyLegacyBank {S with R := (Function.update (Function.update S.R 126 tail) 128 (List.replicate L tick))}).R r.1).length = _
    rw [weightFamilyLegacyBank_key]
    by_cases h128' : r.1 = 128
    · simp [h128',groupHeaderValue]
    have h126 := (groupHeaderSources_off r hr).1
    have hv128 : r.1.val ≠ 128 := by simpa [Fin.ext_iff] using h128'
    simpa [h128',h126,groupHeaderValue,hv128] using hmasters r hr
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := generateHaloWeightClass_exec (body := body)
    P N q l s t u band a b L hP hst hu hband has hbs hL hLs hA v₁ T hmastersT
    (by simpa [T] using ha) (by simpa [T] using hb) hleft (by
      intro k hk hk93 hk110
      have hk126 : k ≠ 126 := by intro he; subst k; norm_num at hk
      have hk128 : k ≠ 128 := by intro he; subst k; norm_num at hk
      simpa [T,weightFamilyLegacyBank_key,hk126,hk128] using hblank k hk hk93 hk110)
    (by simpa [T] using h133) (by
      intro i hi
      have hi126 : i ≠ 126 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      have hi128 : i ≠ 128 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [T,hi126,hi128] using hfresh i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let W : Stacks 151 A := {T with R := Function.update T.R 150 ((weightKeyPacket page).reverse++T.R 150)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 128 v₂ W
  refine ⟨v₃,n₁+(n₂+(2*L+2)),hu₃.trans (hu₂.trans hu₁),by dsimp only [generateHaloWeightLengthKeyCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast ?_ ?_⟩
  · simp [W,T]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi128 : i = 128 <;> by_cases hi150 : i = 150 <;>
      simp [W,T,Function.update_apply,hi128,hi150,h128,page]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
