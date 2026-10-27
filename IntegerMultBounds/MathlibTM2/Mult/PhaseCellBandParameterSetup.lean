module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic
public import IntegerMultBounds.NLogN.PhaseCellBand

/-! Execute the canonical inverse band from p and u, including integer division and square root. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN

def bandRootMap : Fin 4 → Fin 7 := ![3,4,5,6]

theorem bandRootMap_injective : Function.Injective bandRootMap := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [bandRootMap]

def tblBandParameter : TblCode 7 :=
  .seq (tblBlock 7 [.copy 0 2,.add 2 2 2,.add 2 2 2,.add 2 2 2,.add 2 2 2] (.div 2 1 3))
    (tblRootSuccessor.rename bandRootMap)

def bandParameterValues (p u : ℕ) : Fin 7 → ℕ :=
  ![p,u,16*p,16*p/u,16*p/u+1,PhaseCellBand.width p u,(PhaseCellBand.width p u)^2]

theorem tblBandParameter_do {A W e : ℕ} (st : TblSt 7 A) (p u : ℕ)
    (hp : st.val 0 = p) (hu : st.val 1 = u) (hroom : 64*(p+1)+u < 2^W) :
    TblDo A W e tblBandParameter st
      (fun z => z.val = bandParameterValues p u ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2^W)
      (4*PhaseCellBand.width p u+12) := by
  let x := 16*p/u
  have hx : x ≤ 16*p := Nat.div_le_self _ _
  have hrootRoom : 4*(x+1) < 2^W := by omega
  let st₁ : TblSt 7 A := ⟨Function.update (Function.update st.val 2 (16*p)) 3 x,st.acc⟩
  have hinit : TblDo A W e
      (tblBlock 7 [.copy 0 2,.add 2 2 2,.add 2 2 2,.add 2 2 2,.add 2 2 2] (.div 2 1 3)) st
      (fun z => z = st₁) 6 := TblDo.block _ _
    (by simp [tblFitsList,TblIns.fits,TblIns.exact,hp]; omega)
    (by simp [tblExactList,TblIns.exact,st₁,hp,hu,x,show p+p+(p+p)+(p+p+(p+p))+(p+p+(p+p)+(p+p+(p+p))) = 16*p by omega])
  have hroot := (tblRootSuccessor_do (A := A) (W := W) (e := e)
    (st₁.restrict bandRootMap) x (by simp [TblSt.restrict,bandRootMap,st₁]) hrootRoom).rename bandRootMap_injective
  have hr := hinit.seq (fun z hz => by cases hz; exact hroot)
  exact hr.mono (fun z ⟨⟨hz,ha,hfit⟩,hoff⟩ => by
    have hv (i : Fin 4) : z.val (bandRootMap i) = rootSuccessorValues x i := congrFun hz i
    have h0 : z.val 0 = p := (hoff 0 (by intro i; fin_cases i <;> decide)).trans (by simpa [st₁] using hp)
    have h1 : z.val 1 = u := (hoff 1 (by intro i; fin_cases i <;> decide)).trans (by simpa [st₁] using hu)
    have h2 : z.val 2 = 16*p := (hoff 2 (by intro i; fin_cases i <;> decide)).trans (by simp [st₁])
    refine ⟨?_,ha,?_⟩
    · funext i
      fin_cases i <;> first
        | exact h0
        | exact h1
        | exact h2
        | exact hv 0
        | exact hv 1
        | exact hv 2
        | exact hv 3
    · intro i
      fin_cases i
      · change z.val 0 < 2^W; rw [h0]; omega
      · change z.val 1 < 2^W; rw [h1]; omega
      · change z.val 2 < 2^W; rw [h2]; omega
      · exact hfit 0
      · exact hfit 1
      · exact hfit 2
      · exact hfit 3) (by dsimp [PhaseCellBand.width,x]; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
