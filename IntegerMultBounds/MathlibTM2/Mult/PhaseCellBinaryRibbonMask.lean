module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskBankLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskSemantics

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem binaryRibbonMask_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
    {body : P → Pr P 168 Q A U} (boundary : Bool) (value : Fin 168 → ℕ)
    (hs : value 145 = s) (ht : value 146 = t) (hband : value 147 = band)
    (ha : value 149 = a) (hb : value 151 = b) (hindex : value 155 = origin)
    (hcount : value 164 = origin+(N+2*band))
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hfit : origin+N ≤ s)
    (hfitV : origin+(N+2*band)+s < 2^V) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (ribbonMaskBankSource i) < 2^V) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hV : (S.R 163).length = V)
    (hmeta : ∀ i, S.R (ribbonMaskBankSource i) = binSyms V (value (ribbonMaskBankSource i)))
    (hblank : ∀ r, S.R (ribbonTableReg r) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72) ∧
      Exec body (.seq loadRibbonMaskBank (ribbonMaskHost boundary)) (mk v S) m
        (mk v' {S with R := (Function.update S.R 158
          ((couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)++S.R 158))}) := by
  obtain ⟨v₁,hu₁,he₁,hh,hframe⟩ := loadRibbonMaskBank_exec V value hbound v S hV hmeta hblank
  let B : Stacks 168 A := {S with R := chirpBankLoadR ribbonTableReg ribbonMaskBankSource V V value S.R}
  let st : TblSt 18 A := ⟨fun i => value (ribbonMaskBankSource i),[]⟩
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := ribbonMaskHost_exec (body := body) boundary st
    (by simp [st,ribbonMaskBankSource,hs]) (by simp [st,ribbonMaskBankSource,ht])
    (by simp [st,ribbonMaskBankSource,hband]) (by simp [st,ribbonMaskBankSource,ha])
    (by simp [st,ribbonMaskBankSource,hb]) (by simp [st,ribbonMaskBankSource,hindex])
    (by simp [st,ribbonMaskBankSource,hcount]) rfl hst haS hbS hbandS hfit hfitV hwide hbound v₁ B hh
  refine ⟨v₂,152*V+153+m₂,hu₂.trans hu₁,Nat.add_le_add_left hm₂ _,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext r
  by_cases hr : r.val < 33
  · obtain ⟨k,hk⟩ := ribbonTableReg_covers r hr
    have hz : S.R r = [] := hk ▸ hblank k
    have hn : r ≠ 158 := by intro he; have hv := congrArg (fun j : Fin 168 => j.val) he; norm_num at hv; omega
    simp [hr,hn,hz]
  · by_cases ho : r = 158
    · subst r; simp [B,hframe 158 (by decide)]
    · have hf : B.R r = S.R r := hframe r (by omega)
      simp [hr,ho,hf]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
