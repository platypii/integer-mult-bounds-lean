module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateHaloWeightLengthKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyLoop

/-! Generate every numerical page in runtime key order, then restore the
completed packets into the retained family queue. No page is supplied. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def generateHaloWeightKeyStep : Pr P₀ 151 Q A U :=
  .seq (.act (.pop (.rt 127) (fun v _ => v) .done))
    (.seq generateHaloWeightLengthKey (.act (peekR 127)))

def generateHaloWeightFamily : Pr P₀ 151 Q A U :=
  .seq (.loop (·.flag) generateHaloWeightKeyStep) restoreWeightKeyFamily

def generatedWeightFamilyR {A : ℕ} (R : Regs 151 A) (keys count completed : List (Fin (A+4))) : Regs 151 A :=
  Function.update (Function.update (Function.update R 126 keys) 127 count) 150 completed

theorem generatedWeightFamilyR_legacy {A : ℕ} (S : Stacks 151 A) (keys count completed : List (Fin (A+4))) :
    (weightFamilyLegacyBank {S with R := generatedWeightFamilyR S.R keys count completed}).R =
      keyLoopR (weightFamilyLegacyBank S).R keys count ((weightFamilyLegacyBank S).R 132) := by
  funext i
  have hi150 : i.val ≠ 150 := by omega
  by_cases hi132 : i = 132 <;>
    simp [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg,
      generatedWeightFamilyR,keyLoopR,Function.update_apply,Fin.ext_iff,hi150,hi132]

theorem generateHaloWeightFamilyLoop_exec (P N q l s t u band a b V w : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (keys : List ℕ) (hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L < 2^V)
    (raw tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hready : LengthKeyReady P N q l s t u band V w raw (weightFamilyLegacyBank S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hkeys : S.R 126 = lengthKeyPackets A V keys++tail)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (hflag : v.flag = keys.head?.isSome) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (keys.map (fun L => generateHaloWeightLengthKeyCost P N q l s t u band a b V L+3)).sum+1 ∧
      Exec body (.loop (·.flag) generateHaloWeightKeyStep) (mk v S) m
        (mk v' {S with R := (generatedWeightFamilyR S.R tail []
          ((weightKeyFamily (haloWeightKeyPages A (2*q+8) q P s t u band a b keys)).reverse++S.R 150))}) := by
  induction keys generalizing v S with
  | nil =>
    have hk : S.R 126 = tail := by simpa [lengthKeyPackets] using hkeys
    have hc : S.R 127 = [] := by simpa using hcount
    refine ⟨v,1,rfl,by simp,(Exec.loop_false (body := body) (p := generateHaloWeightKeyStep)
      (s := mk v S) (by change v.flag = false; simpa using hflag)).cast rfl ?_⟩
    apply congrArg (mk v)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi126 : i = 126 <;> by_cases hi127 : i = 127 <;> by_cases hi150 : i = 150 <;>
      simp [generatedWeightFamilyR,haloWeightKeyPages,weightKeyFamily,hi126,hi127,hi150,hk,hc]
  | cons L keys ih =>
    obtain ⟨hL,hLs,hfit⟩ := hbounds L (by simp)
    let cs := List.replicate keys.length (tick : Fin (A+4))
    let T : Stacks 151 A := {S with R := Function.update S.R 127 cs}
    have hr := hready.pop_family cs
    have hp : (.pop (.rt 127) (fun v : HS 151 Q A U => fun _ => v) .done : Act 151 Q A U).run
        (mk v S) = mk v T := by simp [Action.run,update_rt,T,cs,hcount,List.replicate_succ]
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateHaloWeightLengthKey_exec (body := body)
      P N q l s t u band a b V L hP hst hu hband has hbs hL hLs hA hfit v T
      (lengthKeyPackets A V keys++tail) hr.keyWidth
      (by simpa [T,lengthKeyPackets,List.append_assoc] using hkeys) hr.masters
      (by simpa [T] using ha) (by simpa [T] using hb) hr.left hr.blank hr.headerTemp (by
        intro i hi
        have hi127 : i ≠ 127 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [show T.R i = S.R i by simp [T,hi127]]
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | (simpa [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hready.fresh 134 (by simp))
          | (simpa [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hready.fresh 135 (by simp))
          | (simpa [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hready.fresh 136 (by simp))
          | (simpa [weightFamilyLegacyBank,embStk,weightFamilyCoreReg,cachedGroupLegacyReg] using hready.fresh 137 (by simp))
          | exact hcache _ (by simp))
    let page := batchWeightPage A (2*q+8) q P s t u (haloLengthGroup s t band a b L).length L
      (fun n => (haloGroupOrigin s t band a b L n).val)
    let W : Stacks 151 A := {S with R := (generatedWeightFamilyR S.R (lengthKeyPackets A V keys++tail) cs
      ((weightKeyPacket page).reverse++S.R 150))}
    have he₁' : Exec body generateHaloWeightLengthKey (mk v T) n₁ (mk v₁ W) := by
      refine he₁.cast rfl ?_
      apply congrArg (mk v₁)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi126 : i = 126 <;> by_cases hi127 : i = 127 <;>
        simp [W,T,generatedWeightFamilyR,Function.update_apply,hi126,hi127,page]
    have hcountW : W.R 127 = cs := by simp [W,generatedWeightFamilyR]
    have ht := Exec.act (body := body) (peekR 127) (mk v₁ W)
    rw [peekR_run,hcountW] at ht
    let vW : HS 151 Q A U := {v₁ with flag := cs.head?.isSome}
    have hstep : Exec body generateHaloWeightKeyStep (mk v S) (n₁+2) (mk vW W) :=
      (Exec.seq (hp ▸ Exec.act (body := body) (.pop (.rt 127) (fun v _ => v) .done) _)
        (Exec.seq he₁' ht)).cast (by omega) rfl
    have hreadyW := hready.of_frame (lengthKeyPackets A V keys++tail) cs ((weightFamilyLegacyBank S).R 132)
      (S' := weightFamilyLegacyBank W) rfl (generatedWeightFamilyR_legacy S _ _ _)
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := ih (fun K hK => hbounds K (by simp [hK])) vW W hreadyW
      (by simpa [W,generatedWeightFamilyR] using ha) (by simpa [W,generatedWeightFamilyR] using hb)
      (by simp [W,generatedWeightFamilyR]) (by simp [W,generatedWeightFamilyR,cs]) (by
        intro i hi
        have hi126 : i ≠ 126 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
        have hi127 : i ≠ 127 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
        have hi150 : i ≠ 150 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
        simpa [W,generatedWeightFamilyR,hi126,hi127,hi150] using hcache i hi)
      (by exact count_head_isSome keys)
    refine ⟨v₂,n₁+2+n₂+1,hu₂.trans hu₁,?_,
      (Exec.loop_true (by change v.flag = true; simpa using hflag) hstep he₂).cast (by omega) ?_⟩
    · simp only [List.map_cons,List.sum_cons]
      omega
    · apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi126 : i = 126 <;> by_cases hi127 : i = 127 <;> by_cases hi150 : i = 150 <;>
        simp [W,generatedWeightFamilyR,Function.update_apply,hi126,hi127,hi150,
          haloWeightKeyPages,weightKeyFamily_cons,List.reverse_append,List.append_assoc,page]

def generateHaloWeightFamilyCost (A P N q l s t u band a b V : ℕ) (keys : List ℕ) : ℕ :=
  (keys.map (fun L => generateHaloWeightLengthKeyCost P N q l s t u band a b V L+3)).sum+
    2*(weightKeyFamily (haloWeightKeyPages A (2*q+8) q P s t u band a b keys)).length+3

theorem generateHaloWeightFamily_exec (P N q l s t u band a b V w : ℕ) [NeZero s]
    (hP : 13 ≤ P) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (keys : List ℕ) (hbounds : ∀ L ∈ keys, 0 < L ∧ L ≤ s ∧ L < 2^V)
    (raw tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hready : LengthKeyReady P N q l s t u band V w raw (weightFamilyLegacyBank S))
    (ha : (S.R 141).length = a) (hb : (S.R 142).length = b)
    (hkeys : S.R 126 = lengthKeyPackets A V keys++tail)
    (hcount : S.R 127 = List.replicate keys.length tick)
    (hcache : ∀ i ∈ ([(144 : Fin 151),145,146,147,149] : List (Fin 151)), S.R i = [])
    (hcomplete : S.R 150 = []) (hflag : v.flag = keys.head?.isSome) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateHaloWeightFamilyCost A P N q l s t u band a b V keys ∧
      Exec body generateHaloWeightFamily (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          126 tail) 127 []) 148 (weightKeyFamily (haloWeightKeyPages A (2*q+8) q P s t u band a b keys)++S.R 148)) 150 [])}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := generateHaloWeightFamilyLoop_exec (body := body)
    P N q l s t u band a b V w hP hst hu hband has hbs hA keys hbounds raw tail v S
    hready ha hb hkeys hcount hcache hflag
  let pages := haloWeightKeyPages A (2*q+8) q P s t u band a b keys
  let T : Stacks 151 A := {S with R := (generatedWeightFamilyR S.R tail []
    ((weightKeyFamily pages).reverse++S.R 150))}
  obtain ⟨v₂,hu₂,he₂⟩ := restoreWeightKeyFamily_exec (body := body) v₁ T pages (S.R 148)
    (by simp [T,generatedWeightFamilyR,hcomplete]) (by simp [T,generatedWeightFamilyR])
  refine ⟨v₂,n₁+(2*(weightKeyFamily pages).length+2),hu₂.trans hu₁,?_,(Exec.seq he₁ he₂).cast rfl ?_⟩
  · dsimp only [generateHaloWeightFamilyCost]
    dsimp only [pages] at *
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi126 : i = 126 <;> by_cases hi127 : i = 127 <;> by_cases hi148 : i = 148 <;> by_cases hi150 : i = 150 <;>
      simp [T,generatedWeightFamilyR,Function.update_apply,hi126,hi127,hi148,hi150,pages]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
