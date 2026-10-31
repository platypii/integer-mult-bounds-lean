module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedLocalHaloController
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock

/-! Generate both origin pages from ordinary retained unary geometry, then release
all private table state. The scan is restricted to the current halo. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U P₀ : Type} {body : P₀ → Pr P₀ 117 Q A U}

def preparedPairedLocalHaloClass : Pr P₀ 117 Q A U :=
  .seq initializeOriginBank (.seq (loadOriginList haloClassHeaderAssignments)
    (.seq pairedLocalHaloController releaseOriginBank))

def preparedPairedLocalHaloClassCost (V s t band a b L : ℕ) :=
  (104*V+137)+haloClassHeadersCost s t band a b L V+
    pairedLocalHaloControllerCost V s t band a b L+(62*V+63)

private theorem loadOriginList_native (rs : List (Fin 117 × Fin 16)) :
    mnNativePushBound 3 (loadOriginList (P₀ := P₀) (Q := Q) (A := A) (U := U) rs) := by
  induction rs with
  | nil => simp [loadOriginList,mnNativePushBound,mnActPush]
  | cons r rs ih =>
    refine ⟨?_,ih⟩
    simp [tblLoad1,bclear,toBinary,bzero,zeroBits,umulSym,scanR,keepIn,eachSym,countIter,incrField,incStep,setCarry,
      moveR,moveStep,whileR,popPush,uclear,drainR,popDo,pushN,peekR,
      mnNativePushBound,mnActPush]

theorem preparedPairedLocalHaloClass_native :
    mnNativePushBound 3 (preparedPairedLocalHaloClass (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  refine ⟨chirpBankLoad_native _ _ _ _,loadOriginList_native _,countedPairedOriginHost_native _,
    clearWords_native_three _⟩

theorem preparedPairedLocalHaloClass_exec_within (V s t band a b L : ℕ)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s) (hL : 0 < L) (hLs : L ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b) (hLSrc : (S.R 102).length = L)
    (hV : (S.R 115).length = V) (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) (depth : ℕ) :
    ∃ v' S' n, v'.user = v.user ∧
      n ≤ preparedPairedLocalHaloClassCost V s t band a b L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*preparedPairedLocalHaloClassCost V s t band a b L) depth preparedPairedLocalHaloClass
        (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      S'.R = Function.update (Function.update (Function.update S.R 109
        ((ScalarPlacement.haloPackedOffsets s t band a b L).flatMap (binSyms V)++S.R 109))
        113 (haloOriginPackets A V s t band a b L++S.R 113))
        116 (List.replicate (haloLengthGroup s t band a b L).length tick) := by
  obtain ⟨v₁, hu₁, he₁, hh₁⟩ := initializeOriginBank_exec (body := body) V v S hV h106
    (fun r => hblank _ (originReg_range r))
  let S₁ : Stacks 117 A := { S with R := chirpBankLoadR originReg (fun _ => 106) V V (fun _ => 0) S.R }
  have hoff₁ (k : Fin 117) (hk : 31 ≤ k.val) : S₁.R k = S.R k := by
    apply chirpBankLoad_off
    intro r he
    have hr := originReg_range r
    rw [he] at hk
    omega
  have hhigh (k : Fin 117) (hk : 31 ≤ k.val) : ∀ r, originReg r ≠ k := by
    intro r he
    have hr := originReg_range r
    rw [he] at hr
    omega
  obtain ⟨v₂, S₂, n₂, hu₂, hn₂, he₂, hh₂, hf₂⟩ := loadHaloClassHeaders_exec (body := body) s t band a b L V v₁ S₁
    (by rw [hoff₁ 97 (by decide)]; exact hsSrc) (by rw [hoff₁ 98 (by decide)]; exact htSrc)
    (by rw [hoff₁ 100 (by decide)]; exact hbSrc)
    (by rw [hoff₁ 111 (by decide)]; exact haSrc) (by rw [hoff₁ 113 (by decide)]; exact hbEndSrc)
    (by rw [hoff₁ 102 (by decide)]; exact hLSrc) hh₁
  have hoff₂ (k : Fin 117) (hk : 31 ≤ k.val) : S₂.R k = S.R k :=
    (hf₂.2.2.2 k (hhigh k hk)).trans (hoff₁ k hk)
  obtain ⟨v₃, S₃, n₃, st₃, hu₃, hn₃, he₃, hambient₃, hout₃, hcount₃, hh₃, hb₃, hi₃, ho₃, hl₃, hf₃⟩ :=
    pairedLocalHaloController_exec_within (body := body) hs hst hband hab hbs hL hLs hwide hA v₂ S₂ hh₂
      (by rw [hoff₂ 104 (by decide)]; exact h104)
      (by rw [hoff₂ 106 (by decide)]; exact h106)
      (by rw [hoff₂ 116 (by decide)]; exact h116) 0
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := releaseOriginBank_exec (body := body) V st₃.val v₃ S₃ hh₃
  let S₄ : Stacks 117 A := { S₃ with R := fun k => if k.val < 31 then [] else S₃.R k }
  have hoff₃ (k : Fin 117) (hk : 31 ≤ k.val) (hk109 : k ≠ 109) (hk113 : k ≠ 113) (hk116 : k ≠ 116) : S₃.R k = S.R k :=
    (hf₃ k hk109 hk113 hk116 (hhigh k hk)).trans (hoff₂ k hk)
  have htime : (104*V+137)+(n₂+(n₃+n₄)) ≤ preparedPairedLocalHaloClassCost V s t band a b L := by
    unfold preparedPairedLocalHaloClassCost
    omega
  refine ⟨v₄, S₄, (104*V+137)+(n₂+(n₃+n₄)), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), htime, ?_, hi₃.trans hf₂.1,
    ho₃.trans hf₂.2.1, hl₃.trans hf₂.2.2.1, ?_⟩
  · exact mn_native_exec_within (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃.toExec he₄)))
      3 preparedPairedLocalHaloClass_native depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3 htime) _)
  · funext k
    by_cases hk109 : k = 109
    · subst k; simpa [S₄, hoff₂ 109 (by decide)] using hout₃
    by_cases hk113 : k = 113
    · subst k; simpa [S₄,hoff₂ 113 (by decide)] using hambient₃
    by_cases hk116 : k = 116
    · subst k; simpa [S₄] using hcount₃
    by_cases hk : k.val < 31
    · simp [S₄, hk, hk109, hblank k hk,hk113,hk116]
    simp [S₄, hk, hk109,hk113,hk116, hoff₃ k (by omega) hk109 hk113 hk116]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
