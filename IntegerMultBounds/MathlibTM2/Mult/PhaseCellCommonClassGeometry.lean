module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonClassInputValues
public import IntegerMultBounds.MathlibTM2.Fast.TableProg
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush

/-! Three table atoms derive each movement class from the shared scalar prefix.
Only core and halo length change; a class length is not a supplied input. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  ScalarPlacement.ComputedClassBanks
variable {T Q A : ℕ} {P U : Type}

def coreRows (clipped : Bool) (s width : ℕ) := if clipped then s%width else width

theorem coreRows_le (clipped : Bool) (s width : ℕ) (hwidth : 0 < width) : coreRows clipped s width ≤ width := by
  cases clipped
  · exact le_rfl
  · exact (Nat.mod_lt s hwidth).le

def haloRows (clipped : Bool) (s width radius : ℕ) := coreRows clipped s width+2*radius

def code (clipped : Bool) : TblCode 13 :=
  tblBlock 13 [if clipped then .mod 4 12 10 else .copy 12 10,.add 9 9 11] (.add 10 11 11)

def loaded (clipped : Bool) (s width radius : ℕ) (st : TblSt 13 A) : TblSt 13 A :=
  ⟨Function.update (Function.update st.val 10 (coreRows clipped s width)) 11 (haloRows clipped s width radius),st.acc⟩

theorem haloRows_mem (clipped : Bool) (s width radius : ℕ) :
    haloRows clipped s width radius ∈ coreGatherLengths s width radius := by
  cases clipped <;> simp [haloRows,coreRows,coreGatherLengths]

theorem haloRows_cases (s width radius H : ℕ) (hH : H ∈ coreGatherLengths s width radius) :
    ∃ clipped, H = haloRows clipped s width radius := by
  simp only [coreGatherLengths,List.mem_dedup,List.mem_cons,List.not_mem_nil,or_false] at hH
  rcases hH with hH | hH
  · exact ⟨false,hH⟩
  · exact ⟨true,hH⟩

theorem code_do (clipped : Bool) (D s width radius : ℕ) (st : TblSt 13 A)
    (hs : st.val 4 = s) (hw : st.val 12 = width) (hr : st.val 9 = radius)
    (hwidth : 0 < width) (hfit : width+2*radius < 2^D) :
    TblDo A D 0 (code clipped) st (fun st' => st' = loaded clipped s width radius st) 3 := by
  let core := coreRows clipped s width
  have hcore : core ≤ width := coreRows_le clipped s width hwidth
  let S₁ : TblSt 13 A := ⟨Function.update st.val 10 core,st.acc⟩
  have h₁ : TblDo A D 0 (.ins (if clipped then .mod 4 12 10 else .copy 12 10)) st (fun st' => st' = S₁) 1 := by
    apply TblDo.insX
    · cases clipped <;> simp [TblIns.fits]
    · cases clipped <;> simp [TblIns.exact,S₁,core,coreRows,hs,hw]
  let S₂ : TblSt 13 A := ⟨Function.update S₁.val 11 (2*radius),st.acc⟩
  have h₂ : TblDo A D 0 (.ins (.add 9 9 11)) S₁ (fun st' => st' = S₂) 1 := by
    apply TblDo.insX
    · simp [TblIns.fits,S₁,hr]; omega
    · simp [TblIns.exact,S₂,S₁,hr,Nat.two_mul]
  let S₃ : TblSt 13 A := ⟨Function.update S₂.val 11 (core+2*radius),st.acc⟩
  have h₃ : TblDo A D 0 (.ins (.add 10 11 11)) S₂ (fun st' => st' = S₃) 1 := by
    apply TblDo.insX
    · simp [TblIns.fits,S₂,S₁]; omega
    · simp [TblIns.exact,S₃,S₂,S₁]
  have h := h₁.seq (fun st₁ he₁ => he₁ ▸ h₂.seq (fun st₂ he₂ => he₂ ▸ h₃))
  simpa only [code,tblBlock,tblStraight,loaded,S₃,S₂,S₁,core,haloRows,Function.update_idem] using h

/-- Both owned words start at zero; the shared width has its own read-only slot. -/
def seedValues (p u l target s t B W N radius width : ℕ) : Fin 13 → ℕ :=
  ![p,u,l,target,s,t,B,W,N,radius,0,0,width]

theorem seed_loaded_values (clipped : Bool) (p u l target s t B W N radius width : ℕ)
    (acc : List (Fin (A+4))) :
    (loaded clipped s width radius ⟨seedValues p u l target s t B W N radius width,acc⟩).val =
      Matrix.vecAppend rfl (commonInputValues p u l target s t B W N radius (haloRows clipped s width radius)) ![width] := by
  funext i
  fin_cases i <;> simp [loaded,seedValues,commonInputValues,Matrix.vecAppend_eq_ite,haloRows]

theorem seed_prefix (clipped : Bool) (p u l target s t B W N radius width : ℕ)
    (i : Fin 12) (h10 : i ≠ 10) (h11 : i ≠ 11) :
    seedValues p u l target s t B W N radius width (Fin.castAdd 1 i) =
      commonInputValues p u l target s t B W N radius (haloRows clipped s width radius) i := by
  have hx10 : Fin.castAdd 1 i ≠ (10 : Fin 13) := by
    intro heq; apply h10; apply Fin.ext; exact congrArg (fun j : Fin 13 => j.val) heq
  have hx11 : Fin.castAdd 1 i ≠ (11 : Fin 13) := by
    intro heq; apply h11; apply Fin.ext; exact congrArg (fun j : Fin 13 => j.val) heq
  have hh := congrFun (seed_loaded_values clipped p u l target s t B W N radius width ([] : List (Fin 4))) (Fin.castAdd 1 i)
  simpa [loaded,Matrix.vecAppend_eq_ite,hx10,hx11,i.isLt] using hh

/-- Compiled execution changes exactly the two class words and restores scratch. -/
theorem exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (clipped : Bool) (D s width radius : ℕ) (st : TblSt 13 A)
    (hs : st.val 4 = s) (hw : st.val 12 = width) (hr : st.val 9 = radius)
    (hwidth : 0 < width) (hfit : width+2*radius < 2^D) (hvalues : ∀ j, st.val j < 2^D)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS T Q A U) (S : Stacks T A) (hholds : tblHolds rg S (tblRho D wl [] st)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 3*tblC D 0 ∧
      tblHolds rg {S with R := (Function.update (Function.update S.R (rg (.v 10)) (binSyms D (coreRows clipped s width)))
          (rg (.v 11)) (binSyms D (haloRows clipped s width radius)))}
        (tblRho D wl [] (loaded clipped s width radius st)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(3*tblC D 0)) depth
        (tblCompile rg (code clipped)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (rg (.v 10)) (binSyms D (coreRows clipped s width)))
          (rg (.v 11)) (binSyms D (haloRows clipped s width radius)))}) := by
  obtain ⟨st',heq,hrun⟩ := (code_do clipped D s width radius st hs hw hr hwidth hfit).host (body := body) (w := 0)
    hinj wl [] hwl rfl (by simp) hvalues
  subst st'
  obtain ⟨v',F,n,hu,hn,hx,hfinal,hframe⟩ := hrun v S hholds
  have hend : F = {S with R := (Function.update (Function.update S.R (rg (.v 10)) (binSyms D (coreRows clipped s width)))
      (rg (.v 11)) (binSyms D (haloRows clipped s width radius)))} := by
    refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r,rfl⟩ := hk
      rw [hfinal r]
      cases r with
      | v i =>
        by_cases h10 : i = 10
        · subst i; simp [tblRho,loaded,hinj.eq_iff]
        by_cases h11 : i = 11
        · subst i; simp [tblRho,loaded]
        · simpa [tblRho,loaded,h10,h11,hinj.eq_iff] using (hholds (.v i)).symm
      | wr => simpa [tblRho,hinj.eq_iff] using (hholds .wr).symm
      | wn => simpa [tblRho,hinj.eq_iff] using (hholds .wn).symm
      | acc => simpa [tblRho,loaded,hinj.eq_iff] using (hholds .acc).symm
      | z i => simpa [tblRho,hinj.eq_iff] using (hholds (.z i)).symm
    · have h10 : k ≠ rg (.v 10) := by intro heq; exact hk ⟨.v 10,heq.symm⟩
      have h11 : k ≠ rg (.v 11) := by intro heq; exact hk ⟨.v 11,heq.symm⟩
      rw [hframe.2.2.2 k (by intro r heq; exact hk ⟨r,heq⟩)]
      simp only [Function.update_of_ne h10,Function.update_of_ne h11]
  rw [hend] at hx hfinal
  exact ⟨v',n,hu,hn,hfinal,mn_native_exec_within hx 3 (tblCompile_native _ _) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn) _)⟩

/-- A single shared seed supplies the exact common-format table for either class. -/
theorem seed_exec_within (body : P → Pr P T Q A U) (rg : TblR 13 → Fin T) (hinj : Function.Injective rg)
    (clipped : Bool) (D p u l target s t B W N radius width : ℕ)
    (hwidth : 0 < width) (hfit : width+2*radius < 2^D)
    (hvalues : ∀ j, seedValues p u l target s t B W N radius width j < 2^D)
    (wl acc : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS T Q A U) (S : Stacks T A)
    (hholds : tblHolds rg S (tblRho D wl [] ⟨seedValues p u l target s t B W N radius width,acc⟩)) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 3*tblC D 0 ∧
      tblHolds rg {S with R := (Function.update (Function.update S.R (rg (.v 10)) (binSyms D (coreRows clipped s width)))
          (rg (.v 11)) (binSyms D (haloRows clipped s width radius)))}
        (tblRho D wl [] ⟨Matrix.vecAppend rfl (commonInputValues p u l target s t B W N radius (haloRows clipped s width radius)) ![width],acc⟩) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(3*tblC D 0)) depth
        (tblCompile rg (code clipped)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R (rg (.v 10)) (binSyms D (coreRows clipped s width)))
          (rg (.v 11)) (binSyms D (haloRows clipped s width radius)))}) := by
  have hstate : loaded clipped s width radius ⟨seedValues p u l target s t B W N radius width,acc⟩ =
      (⟨Matrix.vecAppend rfl (commonInputValues p u l target s t B W N radius (haloRows clipped s width radius)) ![width],acc⟩ : TblSt 13 A) :=
    congrArg (fun values => (⟨values,acc⟩ : TblSt 13 A)) (seed_loaded_values clipped p u l target s t B W N radius width acc)
  obtain ⟨v',n,hu,hn,hfinal,hx⟩ := exec_within body rg hinj clipped D s width radius
    ⟨seedValues p u l target s t B W N radius width,acc⟩
    (by simp [seedValues])
    (by simp [seedValues])
    (by simp [seedValues])
    hwidth hfit hvalues wl hwl v S hholds depth
  rw [hstate] at hfinal
  exact ⟨v',n,hu,hn,hfinal,hx⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CommonClassGeometry
