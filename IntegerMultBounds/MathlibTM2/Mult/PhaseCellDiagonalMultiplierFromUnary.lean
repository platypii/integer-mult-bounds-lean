module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiagonalMultiplierSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallUnaryScalarInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarHeaderStock

/-! Load and compute diagonal multiplier controls from retained unary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
noncomputable section
variable {Q A : ℕ} {P U : Type} {body : P → Pr P tapes Q A U}

def diagonalMultiplierInputs : List (Fin 5 × Fin tapes) :=
  [(0,recovery (.control .precision)),(1,recovery (.control .packet))]

def diagonalMultiplierFromUnary (header word saved tmp carry : Fin tapes) : Pr P tapes Q A U :=
  .seq (installUnaryScalarInputs diagonalMultiplierTable header word saved tmp carry diagonalMultiplierInputs)
    diagonalMultiplierSetup

def diagonalMultiplierFromUnaryCost (B p w : ℕ) : ℕ :=
  ((p+w)*(4*B+10)+2*(8*B+12)+1)+(5*(4*B+4)+2*(8*B+8)+2)+chirpMultiplierSetupCost B 0 p w

theorem diagonalMultiplierFromUnary_native (header word saved tmp carry : Fin tapes) :
    mnNativePushBound 3 (diagonalMultiplierFromUnary (P := P) (Q := Q) (A := A) (U := U) header word saved tmp carry) :=
  ⟨installUnaryScalarInputs_native ..,chirpMultiplierSetup_native ..⟩

theorem diagonalMultiplierFromUnary_exec (header word saved tmp carry : Fin tapes)
    (hheader : ∀ r, diagonalMultiplierTable r ≠ header)
    (hregs : ∀ src ∈ diagonalMultiplierInputs.map Prod.snd,
      [src,diagonalMultiplierTable .wr,word,saved,tmp,header].Nodup)
    (B p w : ℕ) (hpw : p ≤ w) (hw : 1 ≤ w) (hroom : 4*w+2 < 2^B)
    (wl : List (Fin (A+4))) (hwl : wl.length = B) (v : HS tapes Q A U) (S : Stacks tapes A)
    (hp : (S.R (recovery (.control .precision))).length = p)
    (hwide : (S.R (recovery (.control .packet))).length = w)
    (hwidth : S.R (diagonalMultiplierTable .wr) = wl)
    (hblank : ∀ r : TblR 5, r ≠ .wr → S.R (diagonalMultiplierTable r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = [])
    (hcm : ∀ c : CR, S.R (diagonalCr c) = []) :
    ∃ v' M steps, v'.user = v.user ∧
      steps ≤ diagonalMultiplierFromUnaryCost B p w ∧
      Exec body (diagonalMultiplierFromUnary header word saved tmp carry) (Host.mk v S) steps
        (Host.mk v' {M with R := diagonalCounterR p w M.R}) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        3*diagonalMultiplierFromUnaryCost B p w) depth
        (diagonalMultiplierFromUnary header word saved tmp carry) (Host.mk v S) steps
        (Host.mk v' {M with R := diagonalCounterR p w M.R})) ∧
      tblHolds diagonalMultiplierTable M
        (tblRho B wl [] (loadedBinaryState [(0,p),(1,w)] ⟨fun _ => 0,[]⟩)) ∧
      RsbReady (fun r => diagonalCounterR p w M.R (diagonalRole r)) w p ∧
      M.inp = S.inp ∧ M.out = S.out ∧ M.L = S.L ∧
      (∀ k, (∀ r, diagonalMultiplierTable r ≠ k) → M.R k = S.R k) := by
  obtain ⟨v₁,M,steps₁,hu₁,hn₁,he₁,hh₁,hin,hout,hL,hframe⟩ :=
    installUnaryScalarInputs_exec (body := body) diagonalMultiplierTable diagonalMultiplierTable_injective
      header word saved tmp carry hheader diagonalMultiplierInputs hregs B wl hwl v S hwidth hblank hwork
  have hdata : diagonalMultiplierInputs.map (fun a => (a.1,(S.R a.2).length)) = [(0,p),(1,w)] := by
    simp only [diagonalMultiplierInputs,List.map_cons,List.map_nil,hp,hwide]
  rw [hdata] at hh₁
  let st : TblSt 5 A := loadedBinaryState [(0,p),(1,w)] ⟨fun _ => 0,[]⟩
  have hvals : st.val = ![p,w,0,0,0] := by
    funext i; fin_cases i <;> simp [st,loadedBinaryState]
  have hfit : ∀ i, st.val i < 2^B := by
    intro i; rw [hvals]; fin_cases i <;> simp <;> omega
  have hcmM : ∀ c : CR, M.R (diagonalCr c) = [] := by
    intro c
    exact (hframe _ (fun r => diagonalTable_ne_role _ (.cm c))).trans (hcm c)
  obtain ⟨v₂,steps₂,hu₂,hn₂,he₂,hready⟩ := diagonalMultiplierSetup_exec (body := body) (p := p) (w := w)
    wl [] hwl rfl (Nat.zero_le B) st (congrFun hvals 0) (congrFun hvals 1) hw hroom
    (by intro i hi; rw [hvals]; fin_cases i <;> simp_all) hfit v₁ M hh₁ hcmM
  have hcost : binaryHeaderQueueCost S.R B (diagonalMultiplierInputs.map Prod.snd) =
      (p+w)*(4*B+10)+2*(8*B+12)+1 := by
    rw [binaryHeaderQueueCost_eq]
    simp only [diagonalMultiplierInputs,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,hp,hwide]
    ring
  rw [hcost] at hn₁
  have hsteps : steps₁+steps₂ ≤ ((p+w)*(4*B+10)+2*(8*B+12)+1)+(5*(4*B+4)+2*(8*B+8)+2)+chirpMultiplierSetupCost B 0 p w := by
    change steps₁ ≤ _+5*(4*B+4)+2*(8*B+8)+2 at hn₁
    change steps₂ ≤ chirpMultiplierSetupCost B 0 p w at hn₂
    omega
  have hex : Exec body (diagonalMultiplierFromUnary header word saved tmp carry) (Host.mk v S) (steps₁+steps₂)
      (Host.mk v₂ {M with R := diagonalCounterR p w M.R}) := Exec.seq he₁ he₂
  exact ⟨v₂,M,steps₁+steps₂,hu₂.trans hu₁,hsteps,hex,fun depth =>
    mn_native_exec_within hex 3 (diagonalMultiplierFromUnary_native ..) depth _ (by
      change steps₁+steps₂ ≤ diagonalMultiplierFromUnaryCost B p w at hsteps
      omega),hh₁,hready,hin,hout,hL,hframe⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.LocalRecoveryLayout
