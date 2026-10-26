module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeOriginHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIndexCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTablePacketHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeUnaryKey

/-! Compute and materialize a signed-offset query address from ordinary headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def couplingIndexHeaders : List (Fin 117 × Fin 16) := [(97,0),(100,2),(107,7),(105,3)]

def couplingIndexHeaderState (s band i d : ℕ) : TblSt 16 A :=
  ⟨Function.update (Function.update (Function.update (Function.update (fun _ => 0) 0 s) 2 band) 7 i) 3 d,[]⟩

def couplingIndexFromHeaders (negative : Bool) : Pr P₀ 117 Q A U :=
  .seq (initializeOriginHeaders couplingIndexHeaders)
    (.seq (tablePacketHost (couplingIndexCode negative)) (takeUnaryKey 115 109 108 0 1 2 3))

def couplingIndexFromHeadersCost (negative : Bool) (V s band i d : ℕ) : ℕ :=
  (104*V+137)+((s+band+i+d)*(4*V+10)+24*V+41)+
    (6*tblC V V+64*V+65)+(6*couplingIndex negative s band i d+19*V+14)

theorem couplingIndexFromHeaders_exec {V s band i d : ℕ} (negative : Bool) (hA : 4 ≤ A)
    (hs0 : 0 < s) (hi : i < s) (hd : d ≤ band) (hsV : s < 2^V) (hfit : i+band*s+d < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hdSrc : (S.R 105).length = d)
    (hVsrc : (S.R 115).length = V) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingIndexFromHeadersCost negative V s band i d ∧
      Exec body (couplingIndexFromHeaders negative) (mk v S) m
        (mk v' {S with R := Function.update S.R 108 (List.replicate (couplingIndex negative s band i d) tick)}) := by
  let value := fun r : Fin 117 => (S.R r).length
  let st := couplingIndexHeaderState (A := A) s band i d
  have hsep : ∀ r ∈ couplingIndexHeaders, ∀ x, originReg x ≠ r.1 := by
    intro r hr x he
    have hv : 31 ≤ r.1.val := by
      simp only [couplingIndexHeaders,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have hx := originReg_range x
    have hh := congrArg Fin.val he
    omega
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ := initializeOriginHeaders_exec (body := body)
    couplingIndexHeaders hsep V value v S (by intros; rfl) hVsrc h106 hblank
  have hstate : loadedOriginState value couplingIndexHeaders (⟨fun _ => 0,[]⟩ : TblSt 16 A) = st := by
    simp [loadedOriginState,couplingIndexHeaders,st,couplingIndexHeaderState,value,hsSrc,hbSrc,hiSrc,hdSrc]
  rw [hstate] at hh₁
  have hoff (r : Fin 117) (hr : 31 ≤ r.val) : S₁.R r = S.R r :=
    hf₁.2.2.2 r (fun x he => by have hx := originReg_range x; have hv := congrArg Fin.val he; omega)
  have hbandV : band < 2^V := by
    have hb := Nat.le_mul_of_pos_right band hs0
    omega
  have hbound : ∀ r, st.val r < 2^V := by
    intro r
    simp only [st,couplingIndexHeaderState,Function.update_apply]
    split_ifs <;> omega
  have hc := couplingIndexCode_do (V := V) negative st
    (by simp [st,couplingIndexHeaderState]) (by simp [st,couplingIndexHeaderState])
    (by simp [st,couplingIndexHeaderState]) (by simp [st,couplingIndexHeaderState]) hs0 hd hfit
  have hkV : couplingIndex negative s band i d < 2^V := (couplingIndex_lt negative hs0).trans hsV
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := tablePacketHost_exec (body := body) (couplingIndexCode negative) st
    (by simpa only [st,couplingIndexHeaderState,List.append_nil] using hc) hbound hkV hA v₁ S₁ hh₁
  let S₂ : Stacks 117 A := {S₁ with R := (fun r => if r.val < 31 then [] else if r = 109 then
    binSyms V (couplingIndex negative s band i d)++S₁.R 109 else S₁.R r)}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := takeUnaryKey_exec (body := body)
    (width := 115) (src := 109) (dst := 108) (word := 0) (work := 1) (saved := 2) (tmp := 3) (by decide)
    V (couplingIndex negative s band i d) hkV (S.R 109) v₂ S₂
    (by simp [S₂,hoff 115 (by decide),hVsrc]) (by simp [S₂,hoff 109 (by decide)]) (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · simp [S₂,hoff 108 (by decide),h108]
      all_goals simp [S₂])
  have hcost : loadOriginListCost V value couplingIndexHeaders = (s+band+i+d)*(4*V+10)+24*V+41 := by
    simp [loadOriginListCost,couplingIndexHeaders,value,hsSrc,hbSrc,hiSrc,hdSrc]
    ring
  rw [hcost] at hm₁
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,(Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · dsimp only [couplingIndexFromHeadersCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
    funext r
    by_cases hr : r.val < 31
    · have h108' : r ≠ 108 := by intro he; subst r; norm_num at hr
      have h109 : r ≠ 109 := by intro he; subst r; norm_num at hr
      simp [S₂,hr,h108',h109,hblank r hr]
    · by_cases h108' : r = 108
      · subst r; simp
      by_cases h109 : r = 109
      · subst r; simp
      simp [S₂,hr,h108',h109,hoff r (by omega)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
