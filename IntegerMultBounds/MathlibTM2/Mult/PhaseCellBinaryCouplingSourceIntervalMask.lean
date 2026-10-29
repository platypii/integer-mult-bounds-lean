module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryIntervalStreamHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceIntervalMaskHost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Binary geometry is copied into the table bank and restored after mask generation. -/
theorem binaryCouplingSourceIntervalMask_exec {P U : Type} {Q A V s t band a b origin N : ℕ}
    {body : P → Pr P 117 Q A U} (boundary : Bool) (value : Fin 117 → ℕ)
    (hs : value 97 = s) (ht : value 98 = t) (hband : value 100 = band)
    (ha : value 101 = a) (hb : value 103 = b) (hi : value 107 = origin)
    (hc : value 108 = origin+N) (hfit : origin+N ≤ s)
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, value (intervalGuardBankSource i) < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hV : (S.R 115).length = V)
    (hmeta : ∀ i, S.R (intervalGuardBankSource i) = binSyms V (value (intervalGuardBankSource i)))
    (hblank : ∀ r, S.R (intervalGuardReg r) = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ 144*V+145+((29*N+2)*tblC V 1+66*V+2*N+70) ∧
      Exec body (binaryIntervalStreamHost (couplingSourceIntervalMaskCode boundary)) (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (couplingSourceIntervalMaskSymbols boundary A s t band a b origin N++S.R 109))}) := by
  let st : TblSt 17 A := ⟨fun i => value (intervalGuardBankSource i),[]⟩
  have hcode := couplingSourceIntervalMaskCode_do (A := A) (V := V) (w := 1) boundary st
    (by simp [st,intervalGuardBankSource,hs]) (by simp [st,intervalGuardBankSource,ht])
    (by simp [st,intervalGuardBankSource,hband]) (by simp [st,intervalGuardBankSource,ha])
    (by simp [st,intervalGuardBankSource,hb]) (by simp [st,intervalGuardBankSource,hi])
    (by simp [st,intervalGuardBankSource,hc]) hfit hs0 hst haS hbS hwide
  have hmask : (List.range N).flatMap (fun j =>
      tblPairs A 1 (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)
        (if haloMaskAt boundary s t band a b (origin+j) then 1 else 0)) =
      couplingSourceIntervalMaskSymbols boundary A s t band a b origin N := by
    simp only [couplingSourceIntervalMaskSymbols,publicationMaskSymbol]
    exact List.map_eq_flatMap.symm
  rw [hmask] at hcode
  have hVpos : 1 ≤ V := by
    by_cases hz : V = 0
    · have hh := hwide
      rw [hz] at hh
      norm_num at hh
    · omega
  simpa only [couplingSourceIntervalMaskSymbols_length] using
    binaryIntervalStreamHost_exec (body := body) hVpos (couplingSourceIntervalMaskCode boundary)
      value (couplingSourceIntervalMaskSymbols boundary A s t band a b origin N)
      hcode hbound v S hV hmeta hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
