module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedRowCoefficientPacket

/-! Publish only the row headers and prepared constants, leaving preparation scratch private. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def publishPreparedRowPacket (rg : TblR 50 → Fin T) (dst saved tmp : Fin T) : Pr P₀ T Q A U :=
  publishBinaryHeaders rg dst saved tmp preparedRowPacketFields

theorem publishPreparedRowPacket_exec {rg : TblR 50 → Fin T} (hrg : Function.Injective rg)
    (dst saved tmp : Fin T) (hreg : [dst,saved,tmp].Nodup)
    (hsep : ∀ k ∈ [dst,saved,tmp], ∀ r, rg r ≠ k)
    (W P q s t u band i : ℕ) (wl nl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt 50 A) (hready : CoefficientRowReady P q s t u band i st) (hq : st.val 44 = q)
    (v : HS T Q A U) (S : Stacks T A)
    (hS : tblHolds rg S (tblRho W wl nl st)) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 110*W+111 ∧
      Exec body (publishPreparedRowPacket rg dst saved tmp) (mk v S) m
        (mk v' {S with R := Function.update S.R dst (preparedRowPacket A W P q s t u band i++S.R dst)}) := by
  obtain ⟨v',m,hu,hm,he⟩ := publishBinaryHeaders_exec (body := body) hrg dst saved tmp hreg hsep
    preparedRowPacketFields W wl nl hwl st v S hS hsaved htmp
  refine ⟨v',m,hu,?_,?_⟩
  · simp only [preparedRowPacketFields,List.length_cons,List.length_nil] at hm
    nlinarith only [hm]
  · simpa [publishPreparedRowPacket,preparedRowPacketFields,preparedRowPacket,preparedRowPacketArguments,
      hready.pi,hready.precision,hready.sign,hready.dimension,hready.period,hready.parameter,
      hready.source,hready.grid,hready.scale,hready.bandwidth,hq] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
