module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBorrowBinaryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishBinaryHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientFromHeaders

/-! The retained row-header packet loads in time depending on bit width, not geometry values. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def rowCoefficientPacketFields : List (Fin 50) := [37,19,44,34,35,36,49]

def rowCoefficientPacketArguments (P q s t u band i : ℕ) : List (Fin 50 × ℕ) :=
  [(37,i),(19,P),(44,q),(34,s),(35,t),(36,u),(49,band)]

def rowCoefficientPacket (A W P q s t u band i : ℕ) : List (Fin (A+4)) :=
  (rowCoefficientPacketArguments P q s t u band i).flatMap (fun r => binSyms W r.2)

@[simp] theorem rowCoefficientPacket_length (A W P q s t u band i : ℕ) :
    (rowCoefficientPacket A W P q s t u band i).length = 7*W := by
  simp [rowCoefficientPacket,rowCoefficientPacketArguments]
  omega

theorem loadedBinaryState_rowCoefficientPacket {A : ℕ} (P q s t u band i : ℕ) :
    loadedBinaryState (rowCoefficientPacketArguments P q s t u band i) (⟨fun _ => 0,[]⟩ : TblSt 50 A) =
      rowCoefficientHeaderState P q s t u band i := by
  simp only [rowCoefficientPacketArguments,loadedBinaryState,rowCoefficientHeaderState]
  congr 1
  funext r
  simp only [Function.update_apply]
  split_ifs <;> simp_all

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def publishRowCoefficientPacket (rg : TblR 50 → Fin T) (dst saved tmp : Fin T) : Pr P₀ T Q A U :=
  publishBinaryHeaders rg dst saved tmp rowCoefficientPacketFields

theorem publishRowCoefficientPacket_exec {rg : TblR 50 → Fin T} (hrg : Function.Injective rg)
    (dst saved tmp : Fin T) (hreg : [dst,saved,tmp].Nodup)
    (hsep : ∀ k ∈ [dst,saved,tmp], ∀ r, rg r ≠ k)
    (W P q s t u band i : ℕ) (wl nl : List (Fin (A+4))) (hwl : wl.length = W)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl (rowCoefficientHeaderState P q s t u band i)))
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 70*W+71 ∧
      Exec body (publishRowCoefficientPacket rg dst saved tmp) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (rowCoefficientPacket A W P q s t u band i++S.R dst)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := publishBinaryHeaders_exec (body := body) hrg dst saved tmp hreg hsep
    rowCoefficientPacketFields W wl nl hwl (rowCoefficientHeaderState P q s t u band i) v S hS hsaved htmp
  refine ⟨v',m,hu,?_,?_⟩
  · simp only [rowCoefficientPacketFields,List.length_cons,List.length_nil] at hm
    nlinarith only [hm]
  · simpa [publishRowCoefficientPacket,rowCoefficientPacketFields,rowCoefficientPacket,
      rowCoefficientPacketArguments,rowCoefficientHeaderState] using he

def borrowRowCoefficientPacket (rg : TblR 50 → Fin T) (src work count saved tmp : Fin T) : Pr P₀ T Q A U :=
  borrowBinaryHeaders rg src work count saved tmp rowCoefficientPacketFields

theorem borrowRowCoefficientPacket_exec {rg : TblR 50 → Fin T} (hrg : Function.Injective rg)
    (src work count saved tmp : Fin T) (hreg : [src,work,count,saved,tmp].Nodup)
    (hsep : ∀ k ∈ [src,work,count,saved,tmp], ∀ r, rg r ≠ k)
    (W P q s t u band i : ℕ) (wl nl : List (Fin (A+4))) (hwl : wl.length = W)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl ⟨fun _ => 0,[]⟩))
    (hsrc : S.R src = rowCoefficientPacket A W P q s t u band i++tail)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' S' m, v'.user = v.user ∧ m ≤ 144*W+73 ∧
      Exec body (borrowRowCoefficientPacket rg src work count saved tmp) (mk v S) m (mk v' S') ∧
      tblHolds rg S' (tblRho W wl nl (rowCoefficientHeaderState P q s t u band i)) ∧ tblFr rg S S' := by
  obtain ⟨v',S',m,hu,hm,he,hh,hf⟩ := borrowBinaryHeaders_exec (body := body) hrg src work count saved tmp
    hreg hsep (rowCoefficientPacketArguments P q s t u band i) W wl nl hwl ⟨fun _ => 0,[]⟩ tail v S hS hsrc
    hcount hsaved htmp
  refine ⟨v',S',m,hu,?_,?_,?_,hf⟩
  · simp only [rowCoefficientPacketArguments,List.length_cons,List.length_nil] at hm
    nlinarith only [hm]
  · simpa [borrowRowCoefficientPacket,borrowBinaryHeaders,rowCoefficientPacketArguments,rowCoefficientPacketFields] using he
  · simpa only [loadedBinaryState_rowCoefficientPacket] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
