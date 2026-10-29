module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreHaloPacketCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTablePacketHost
public import IntegerMultBounds.MathlibTM2.Host.Embed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def coreHaloPacketReg (i : Fin 117) : Fin 168 :=
  if i = 109 then 159 else ⟨i.val,by omega⟩

theorem coreHaloPacketReg_injective : Function.Injective coreHaloPacketReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 168 => k.val) he
  simp only [coreHaloPacketReg] at hv
  split_ifs at hv <;> simp_all only
  all_goals first | exact Fin.ext hv | omega

def generatedCoreHaloPacketHost : Pr P 168 Q A U :=
  embProg coreHaloPacketReg Empty.elim (tablePacketHost (P₀ := Empty) generatedCoreHaloPacketCode)

theorem generatedCoreHaloPacketHost_exec {V s width band n : ℕ}
    (st : TblSt 16 A) (hs : st.val 0 = s) (hw : st.val 1 = width) (hr : st.val 2 = n*band)
    (hwidth : 0 < width) (hwide : s+width+n*band < 2^V)
    (hbound : ∀ i, st.val i < 2^V) (hacc : st.acc = []) (hA : 4 ≤ A)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hS : tblHolds originReg (embStk coreHaloPacketReg S)
      (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (17*((s+width-1)/width)+9)*tblC V V+
        (4*((s+width-1)/width)+62)*V+65 ∧
      Exec body generatedCoreHaloPacketHost (mk v S) m
        (mk v' {S with R := fun k => if k.val < 31 then [] else if k = 159 then
          (coreHaloPacketValues s width band n).flatMap (binSyms V)++S.R 159 else S.R k}) := by
  have hfit : ∀ x ∈ coreHaloPacketValues s width band n, x < 2^V := by
    intro x hx
    obtain ⟨k,_,hx⟩ := List.mem_flatMap.mp hx
    have hb := coreHaloEndpoints_bounds s width k band n
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> omega
  have hc := (generatedCoreHaloPacketCode_do (A := A) (W := V) (w := V) st hs hw hr hwidth hwide).mono
    (fun st' he => by simpa only [hacc,List.append_nil] using he) le_rfl
  obtain ⟨vi,m,hui,hm,hei⟩ := tablePacketHost_list_exec (body := fun p : Empty => nomatch p)
    (coreHaloPacketValues s width band n) generatedCoreHaloPacketCode st hc hbound hfit hA
    (embDn coreHaloPacketReg v) (embStk coreHaloPacketReg S) hS
  obtain ⟨v',hv,hu,he⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    coreHaloPacketReg_injective (fun p => nomatch p) hei v rfl S rfl
  have hlen : (coreHaloPacketValues s width band n).length = 2*((s+width-1)/width) := by
    simp [coreHaloPacketValues,coreIndices,List.length_flatMap,Nat.mul_comm]
  refine ⟨v',m,hu.trans hui,by rw [hlen] at hm; nlinarith only [hm],he.cast rfl ?_⟩
  apply congrArg (mk v')
  let F : Stacks 117 A := {embStk coreHaloPacketReg S with R := (fun r =>
    if r.val < 31 then [] else if r = 109 then
      (coreHaloPacketValues s width band n).flatMap (binSyms V)++(embStk coreHaloPacketReg S).R 109
    else (embStk coreHaloPacketReg S).R r)}
  refine Stacks.ext rfl rfl ?_ ?_
  · funext k
    by_cases hx : ∃ r, coreHaloPacketReg r = k
    · obtain ⟨r,rfl⟩ := hx
      exact congrArg (fun B : Stacks 117 A => B.L r)
        (embStk_ovr coreHaloPacketReg_injective F S)
    · exact (embOvr_off (e := coreHaloPacketReg) F.get S (fun i he => hx ⟨i,he⟩)).1
  funext k
  by_cases hx : ∃ r, coreHaloPacketReg r = k
  · obtain ⟨r,rfl⟩ := hx
    have hp := congrArg (fun B : Stacks 117 A => B.R r)
      (embStk_ovr coreHaloPacketReg_injective F S)
    change (embOvr coreHaloPacketReg F.get S).R (coreHaloPacketReg r) = _
    change (embOvr coreHaloPacketReg F.get S).R (coreHaloPacketReg r) = F.R r at hp
    rw [hp]
    by_cases h109 : r = 109
    · subst r; simp [F,embStk,coreHaloPacketReg]
    · have hn : (⟨r.val,by omega⟩ : Fin 168) ≠ 159 := by
        intro he; have hv := congrArg (fun j : Fin 168 => j.val) he; change r.val = 159 at hv; have hr := r.isLt; omega
      simp [F,embStk,coreHaloPacketReg,h109,hn]
  · have hoff := (embOvr_off (e := coreHaloPacketReg) F.get S (fun i he => hx ⟨i,he⟩)).2
    have hn159 : k ≠ 159 := by intro he; apply hx; exact ⟨109,by simpa [coreHaloPacketReg] using he.symm⟩
    have hnlow : ¬ k.val < 31 := by
      intro hk
      apply hx
      refine ⟨⟨k.val,by omega⟩,?_⟩
      simp [coreHaloPacketReg,Fin.ext_iff,show k.val ≠ 109 by omega]
    simpa [hn159,hnlow] using hoff

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
