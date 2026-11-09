module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedWeightInit
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightHostStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Shared weight initialization keeps its table reserve separate from header traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem loadCoefficientList_native (rs : List (Fin 117 × Fin 48)) :
    mnNativePushBound 3 (loadCoefficientList (P₀ := P₀) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    refine ⟨?_,ih⟩
    simp [tblLoad1,toBinary,bzero,zeroBits,eachSym,countIter,incrField,incStep,setCarry,
      bclear,uclear,umulSym,popPush,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]

def sharedWeightInitWorkspace (P s t u q L w : ℕ) : ℕ :=
  let V := weightWorkspaceWidth P q w t u
  18*weightWidthCost P q w t u+(3*(292*V+4*w+393)+
    (3*weightHeadersCost P s t u q L 0 V+3*tblC V w))

theorem sharedWeightInit_trace_within (P s t u q L w m₁ m₃ m₄ : ℕ)
    (v₀ v₁ v₂ v₃ v₄ : HS 117 Q A U) (S₀ S₁ S₂ S₃ S₄ : Stacks 117 A)
    (h₁ : Exec body generateWeightWidth (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : Exec body initializeCoefficientBank (mk v₁ S₁)
      (292*weightWorkspaceWidth P q w t u+4*w+393) (mk v₂ S₂))
    (h₃ : Exec body loadWeightHeaders (mk v₂ S₂) m₃ (mk v₃ S₃))
    (h₄ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₃ S₃)+depth+3*tblC (weightWorkspaceWidth P q w t u) w)
      depth retainedWeightInit (mk v₃ S₃) m₄ (mk v₄ S₄))
    (hm₁ : m₁ ≤ weightWidthCost P q w t u)
    (hm₃ : m₃ ≤ weightHeadersCost P s t u q L 0 (weightWorkspaceWidth P q w t u)) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+sharedWeightInitWorkspace P s t u q L w)
      depth sharedWeightInit (mk v₀ S₀)
      (m₁+((292*weightWorkspaceWidth P q w t u+4*w+393)+(m₃+m₄))) (mk v₄ S₄) := by
  have ht₁ := mn_native_exec_within h₁ 18 generateWeightWidth_native depth
    (mnSize (mk v₀ S₀)+depth+18*weightWidthCost P q w t u) (by omega)
  have ht₂ := mn_native_exec_within h₂ 3 (chirpBankLoad_native _ _ _ _) depth
    (mnSize (mk v₁ S₁)+depth+3*(292*weightWorkspaceWidth P q w t u+4*w+393)) (by omega)
  have ht₃ := mn_native_exec_within h₃ 3 (loadCoefficientList_native _) depth
    (mnSize (mk v₂ S₂)+depth+3*weightHeadersCost P s t u q L 0 (weightWorkspaceWidth P q w t u)) (by omega)
  exact mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (mn_seq_within_add ht₃ (h₄ depth)))

theorem sharedWeightInit_exec_within (P s t u q L w : ℕ) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hw : (S.R 94).length = w)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(104 : Fin 117), 106, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : L ≤ s) :
    let V := weightWorkspaceWidth P q w t u
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ sharedWeightInitCost P s t u q L w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+sharedWeightInitWorkspace P s t u q L w)
        depth sharedWeightInit (mk v S) m (mk v' S')) ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 115 = List.replicate V tick ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k.val ≥ 63 → k ≠ 115 → S'.R k = S.R k := by
  let V := weightWorkspaceWidth P q w t u
  have hlow (k : Fin 117) (hk : k.val < 63) : S.R k = [] := by
    obtain ⟨r, rfl⟩ := coefficientReg_covers k hk
    exact hblank r
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateWeightWidth_exec (body := body) P q w t u v S
    hP' hq hw ht' hu' (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hlow _ (by decide) | exact hfresh _ (by simp))
  let Sw : Stacks 117 A := { S with R := Function.update S.R 115 (List.replicate V tick) }
  obtain ⟨v₂, hu₂, he₂, hh₂⟩ := initializeCoefficientBank_exec (body := body) V w v₁ Sw
    (by simp [Sw]) (by simpa [Sw] using hw) (by simpa [Sw] using hfresh 106 (by simp)) (by
      intro r
      have hn : coefficientReg r ≠ (115 : Fin 117) := by
        intro he; have hr := coefficientReg_range r; rw [he] at hr; omega
      simpa [Sw, hn] using hblank r)
  let S₂ : Stacks 117 A := { Sw with R := chirpBankLoadR coefficientReg (fun _ => 106) V w (fun _ => 0) Sw.R }
  have hoff₂ (k : Fin 117) (hk : 63 ≤ k.val) : S₂.R k = Sw.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := coefficientReg_range r
    rw [he] at hk
    omega
  obtain ⟨v₃, S₃, m₃, hu₃, hm₃, he₃, hh₃, hf₃⟩ := loadWeightHeaders_exec (body := body)
    P s t u q L 0 V w v₂ S₂
    (by rw [hoff₂ 114 (by decide)]; simpa [Sw] using hP')
    (by rw [hoff₂ 97 (by decide)]; simpa [Sw] using hs')
    (by rw [hoff₂ 98 (by decide)]; simpa [Sw] using ht')
    (by rw [hoff₂ 99 (by decide)]; simpa [Sw] using hu')
    (by rw [hoff₂ 112 (by decide)]; simpa [Sw] using hq)
    (by rw [hoff₂ 111 (by decide)]; simp [Sw, hfresh 111 (by simp)])
    (by rw [hoff₂ 102 (by decide)]; simpa [Sw] using hL') hh₂
  have hoff₃ (k : Fin 117) (hk : 63 ≤ k.val) : S₃.R k = Sw.R k := by
    rw [hf₃.2.2.2 k (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)]
    exact hoff₂ k hk
  obtain ⟨v₄, S₄, m₄, st₄, hu₄, hm₄, he₄, hr₄, hh₄, hf₄⟩ := retainedWeightInit_exec_within (body := body)
    (weightHeaderState (A := A) P s t u q L 0) (by simp [weightHeaderState]) (by simp [weightHeaderState])
    (by simp [weightHeaderState]) (by simp [weightHeaderState]) (by simp [weightHeaderState])
    (by simp [weightHeaderState]) hP hs hst hu hL rfl (weightHeaderState_fits hP hs hst hu hs hL)
    rfl v₃ S₃ hh₃
  have hoff₄ (k : Fin 117) (hk : 63 ≤ k.val) : S₄.R k = Sw.R k := by
    rw [hf₄.2.2.2 k (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)]
    exact hoff₃ k hk
  refine ⟨v₄, S₄, m₁+((292*V+4*w+393)+(m₃+m₄)), st₄,
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_,
    hr₄, hh₄, ?_, hf₄.1.trans hf₃.1, hf₄.2.1.trans hf₃.2.1, hf₄.2.2.1.trans hf₃.2.2.1, ?_⟩
  · dsimp only [sharedWeightInitCost]
    dsimp only [V] at *
    omega
  · intro depth
    exact sharedWeightInit_trace_within P s t u q L w m₁ m₃ m₄
      v v₁ v₂ v₃ v₄ S Sw S₂ S₃ S₄ he₁ he₂ he₃ he₄ hm₁ hm₃ depth
  · rw [hoff₄ 115 (by decide)]; simp [Sw, V]
  · intro k hk hk115
    rw [hoff₄ k hk]
    simp [Sw, hk115]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
