module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseScalarSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! Install the retained inverse's ordinary master headers from the computed scalar bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def inverseHeaderSource : Fin 10 → Fin 25 := ![21,19,18,2,4,5,1,11,6,7]

def inverseHeaderAssignments {T : ℕ} (ports : Fin 10 → Fin T) : List (Fin 25 × Fin T) :=
  (List.finRange 10).map (fun i => (inverseHeaderSource i,ports i))

noncomputable def inverseMasterValues (p u l target s t a b : ℕ) [NeZero s] : Fin 10 → ℕ :=
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let E := inverseExecutionExponent p l target N band
  ![2^15*p,2*E+1,4*E,l,s,t,u,band,a,b]

def inverseMasterCopyCost (W : ℕ) (values : Fin 10 → ℕ) : ℕ :=
  ((List.finRange 10).map (fun i => 6*values i+11*W+6)).sum+1

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def installInverseHeaders (rg : TblR 25 → Fin T) (ports : Fin 10 → Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg tblInverseScalars) (tblUnaryCopies rg (inverseHeaderAssignments ports))

theorem installInverseHeaders_exec (rg : TblR 25 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 10 → Fin T) (hports : Function.Injective ports)
    (hsep : ∀ i r, rg r ≠ ports i)
    {W p u l target s t a b : ℕ} [NeZero s] (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl [] st)) :
    ∃ v' S' n z, v'.user = v.user ∧
      n ≤ inverseScalarAtoms p s t u a b*tblC W 0+
        inverseMasterCopyCost W (inverseMasterValues p u l target s t a b) ∧
      Exec body (installInverseHeaders rg ports) (mk v S) n (mk v' S') ∧
      tblHolds rg S' (tblRho W wl [] z) ∧
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.acc = st.acc ∧ (∀ i, z.val i < 2^W) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (ports i) = List.replicate (inverseMasterValues p u l target s t a b i) Node.tick++S.R (ports i)) ∧
      ∀ k, (∀ r, rg r ≠ k) → (∀ i, ports i ≠ k) → S'.R k = S.R k := by
  have hc := tblInverseScalars_do (A := A) (W := W) (e := 0) st h0 h1 h2 h3 h4 h5 h6 h7
    hst haS hbS hbandS hbandRoom hgeometryRoom hprecisionRoom hfit
  obtain ⟨z,⟨hkeep,hband,hN,hE,hq,hstage,hw,hP,hacc,hfitZ⟩,hrun⟩ := hc.host (body := body) hrg wl [] hwl rfl
    (Nat.zero_le W) hfit
  have hvalue (i : Fin 10) : z.val (inverseHeaderSource i) = inverseMasterValues p u l target s t a b i := by
    fin_cases i
    · exact hP
    · exact hstage
    · exact hq
    · exact (hkeep 2).trans h2
    · exact (hkeep 4).trans h4
    · exact (hkeep 5).trans h5
    · exact (hkeep 1).trans h1
    · exact hband
    · exact (hkeep 6).trans h6
    · exact (hkeep 7).trans h7
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hframe⟩ := hrun v S hS
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := tblUnaryCopies_exec (body := body) hrg wl [] z hfitZ
    (inverseHeaderAssignments ports) (by
      intro x hx r
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact hsep i r) v₁ S₁ hh₁
  let S₂ : Stacks T A := {S₁ with R := unaryCopiesR z.val S₁.R (inverseHeaderAssignments ports)}
  have hcost : unaryCopiesCost W z.val (inverseHeaderAssignments ports) =
      inverseMasterCopyCost W (inverseMasterValues p u l target s t a b) := by
    simp only [unaryCopiesCost,inverseHeaderAssignments,List.map_map,inverseMasterCopyCost]
    simp only [Function.comp_def,hvalue]
  refine ⟨v₂,S₂,n₁+n₂,z,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,hkeep,hacc,hfitZ,
    hframe.1,hframe.2.1,hframe.2.2.1,?_,?_⟩
  · exact Nat.add_le_add hn₁ (hn₂.trans_eq hcost)
  · intro r
    rw [show S₂.R (rg r) = S₁.R (rg r) from unaryCopiesR_off z.val S₁.R _ _ (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact (hsep i r).symm)]
    exact hh₁ r
  · intro i
    have hnd : ((inverseHeaderAssignments ports).map Prod.snd).Nodup := by
      simpa only [inverseHeaderAssignments,List.map_map,Function.comp_def] using (List.nodup_finRange 10).map hports
    have hh := unaryCopiesR_at z.val S₁.R (inverseHeaderAssignments ports) hnd
      (inverseHeaderSource i,ports i) (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
    change S₂.R (ports i) = _ at hh
    rw [hh,hvalue,hframe.2.2.2 (ports i) (hsep i)]
  · intro k hk hp
    exact (unaryCopiesR_off z.val S₁.R _ k (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      exact hp i)).trans (hframe.2.2.2 k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
