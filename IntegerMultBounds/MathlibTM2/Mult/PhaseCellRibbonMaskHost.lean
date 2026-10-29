module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableStreamHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRibbonMaskSemantics

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def ribbonTableReg : TblR 18 → Fin 168
  | .v i => ⟨i.val,by omega⟩
  | .wr => 18 | .wn => 19 | .acc => 20
  | .z i => ⟨21+i.val,by omega⟩

theorem ribbonTableReg_injective : Function.Injective ribbonTableReg := by
  intro i j he
  cases i <;> cases j <;> simp_all [ribbonTableReg,Fin.ext_iff]
  all_goals omega

def ribbonTablePorts : List (Fin 168) := List.ofFn (fun i : Fin 33 => (⟨i.val,by omega⟩ : Fin 168))

theorem mem_ribbonTablePorts (k : Fin 168) : k ∈ ribbonTablePorts ↔ k.val < 33 := by
  simp only [ribbonTablePorts,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩; exact i.isLt
  · intro hk; exact ⟨⟨k.val,hk⟩,Fin.ext rfl⟩

theorem ribbonTableReg_range (r : TblR 18) : (ribbonTableReg r).val < 33 := by
  cases r <;> simp [ribbonTableReg] <;> omega

theorem ribbonTableReg_covers (k : Fin 168) (hk : k.val < 33) : ∃ r, ribbonTableReg r = k := by
  by_cases hv : k.val < 18
  · exact ⟨.v ⟨k.val,hv⟩,Fin.ext rfl⟩
  by_cases h18 : k.val = 18
  · exact ⟨.wr,Fin.ext h18.symm⟩
  by_cases h19 : k.val = 19
  · exact ⟨.wn,Fin.ext h19.symm⟩
  by_cases h20 : k.val = 20
  · exact ⟨.acc,Fin.ext h20.symm⟩
  exact ⟨.z ⟨k.val-21,by omega⟩,Fin.ext (by simp [ribbonTableReg]; omega)⟩

def ribbonMaskHost {P U : Type} {Q A : ℕ} (boundary : Bool) : Pr P 168 Q A U :=
  tableStreamHost ribbonTableReg ribbonTablePorts 158 (ribbonMaskCode boundary)

theorem ribbonMaskHost_exec {P U : Type} {Q A V s t band a b origin N : ℕ} [NeZero s]
    {body : P → Pr P 168 Q A U} (boundary : Bool) (st : TblSt 18 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hindex : st.val 16 = origin)
    (hcount : st.val 17 = origin+(N+2*band)) (hacc : st.acc = [])
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hfit : origin+N ≤ s)
    (hfitV : origin+(N+2*band)+s < 2^V) (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hS : tblHolds ribbonTableReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72 ∧
      Exec body (ribbonMaskHost boundary) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 33 then [] else if r = 158 then
          (couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)++S.R r else S.R r}) := by
  have hV : 1 ≤ V := by
    by_contra h
    have : V = 0 := by omega
    subst V; norm_num at hwide <;> omega
  have hc := ribbonMaskCode_do (A := A) (V := V) (w := 1) boundary st hs ht hband ha hb hindex hcount
    (NeZero.pos s) hst haS hbS hbandS hfitV hwide
  have hflags := couplingRibbonFlags_eq_map boundary hst band a b origin N hbS hbandS hfit
  have hlen : (couplingRibbonFlags (s := s) boundary t band a b origin N).length = N+2*band := by
    rw [hflags]; simp
  have hmask : (List.range (N+2*band)).flatMap (fun j =>
      tblPairs A 1 (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b ((origin+j+s-band)%s) then 1 else 0)
        (if IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloMaskAt boundary s t band a b ((origin+j+s-band)%s) then 1 else 0)) =
      (couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag) := by
    rw [hflags]
    simp only [List.map_map,Function.comp_def,publicationMaskSymbol]
    exact List.map_eq_flatMap.symm
  rw [hmask] at hc
  have hnd : ribbonTablePorts.Nodup := by
    apply List.nodup_ofFn.mpr
    intro i j he; exact Fin.ext (congrArg (fun k : Fin 168 => k.val) he)
  have he := tableStreamHost_exec (body := body) ribbonTableReg ribbonTableReg_injective ribbonTablePorts hnd
    (fun k hk => ribbonTableReg_covers k ((mem_ribbonTablePorts k).mp hk))
    (fun r => (mem_ribbonTablePorts _).mpr (ribbonTableReg_range r))
    158 (by rw [mem_ribbonTablePorts]; decide) hV (ribbonMaskCode boundary) st _ hacc hc hbound v S hS
  simp only [mem_ribbonTablePorts] at he
  simpa [ribbonMaskHost,ribbonTablePorts,hlen,Nat.add_assoc] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
