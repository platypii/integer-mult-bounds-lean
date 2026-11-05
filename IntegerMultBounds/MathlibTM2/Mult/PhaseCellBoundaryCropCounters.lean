module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCropMetadata
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellParameterArithmetic

/-! Execute boundary metadata and materialize its bit counts as unary controls.
The existing structural counter exporter restores binary inputs and scratch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def counterProgram (rg : TblR 9 → Fin T) (last : Bool) (skip count : Fin T) : Pr P T Q A U :=
  .seq (tblCompile rg (code last)) (tblUnaryCopies rg [(7,skip),(8,count)])

theorem counters_exec (rg : TblR 9 → Fin T) (hinj : Function.Injective rg)
    (last : Bool) (skip count : Fin T) (hne : skip ≠ count)
    (hskip : ∀ r, rg r ≠ skip) (hcount : ∀ r, rg r ≠ count)
    (D s width W : ℕ) (st : TblSt 9 A)
    (hs : st.val 0 = s) (hw : st.val 1 = width) (hW : st.val 2 = W)
    (hwidth : 0 < width) (hword : 0 < W) (hroom : 3*width < s)
    (hfit : s*W < 2^D) (hvalues : ∀ j, st.val j < 2^D)
    (wl : List (Fin (A+4))) (hwl : wl.length = D)
    (v : HS T Q A U) (S : Stacks T A) (hholds : tblHolds rg S (tblRho D wl [] st)) :
    ∃ v' F n z, v'.user = v.user ∧ n ≤ 10*tblC D 0+6*(s*W)+22*D+13 ∧
      Exec body (counterProgram rg last skip count) (mk v S) n (mk v' F) ∧
      tblHolds rg F (tblRho D wl [] z) ∧
      (∀ i : Fin 3, z.val (Fin.castAdd 6 i) = st.val (Fin.castAdd 6 i)) ∧ z.acc = st.acc ∧
      (∀ j, z.val j < 2^D) ∧
      F.R skip = List.replicate (coreStart width (index last s width)*W) tick++S.R skip ∧
      F.R count = List.replicate (coreLength s width (index last s width)*W) tick++S.R count ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, (∀ r, rg r ≠ k) → k ≠ skip → k ≠ count → F.R k = S.R k := by
  have hc := tblDo_with_fits (code_do last D s width W A st hs hw hW hwidth hword hroom hfit) hvalues
  obtain ⟨z,⟨heq,hfitZ⟩,hrun⟩ := hc.host (body := body) hinj wl [] hwl rfl (Nat.zero_le D) hvalues
  have hspec := (run_spec last D s width W A st hs hw hW hwidth hword hroom hfit).2
  rw [←heq] at hspec
  have hkeep := run_inputs last A st
  rw [←heq] at hkeep
  obtain ⟨v₁,S₁,n₁,hu₁,hn₁,he₁,hh₁,hframe⟩ := hrun v S hholds
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := tblUnaryCopies_exec (body := body) hinj wl [] z hfitZ
    [(7,skip),(8,count)] (by
      intro p hp r
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · exact hskip r
      · exact hcount r) v₁ S₁ hh₁
  simp only [List.length_nil] at hn₁
  let F : Stacks T A := {S₁ with R := unaryCopiesR z.val S₁.R [(7,skip),(8,count)]}
  have hstable (k : Fin T) (hk : k ≠ skip) (hk' : k ≠ count) : F.R k = S₁.R k := by
    simp only [F,unaryCopiesR,Function.update_of_ne hk,Function.update_of_ne hk']
  have hvolume : coreStart width (index last s width)+coreLength s width (index last s width) ≤ s := by
    have hi := index_eq_boundary last s width hwidth hroom
    have hv := (boundaryCropSchedule_spec s width hwidth hroom).2.2
    have hm : boundaryCropIndex s width (if last then 2 else 1) ∈ boundaryCropSchedule s width := by
      cases last <;> simp [boundaryCropIndex,boundaryCropSchedule]
    have hstart := (hv _ hm).2.1
    rw [←hi] at hstart
    have hlen : coreLength s width (index last s width) ≤ s-coreStart width (index last s width) := min_le_right _ _
    omega
  have hbits := Nat.mul_le_mul_right W hvolume
  rw [Nat.add_mul] at hbits
  have hcost : unaryCopiesCost D z.val [(7,skip),(8,count)] ≤ 6*(s*W)+22*D+13 := by
    simp only [unaryCopiesCost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hspec.1,hspec.2]
    omega
  refine ⟨v₂,F,n₁+n₂,z,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,?_,hkeep.1,hkeep.2,hfitZ,?_,?_,
    hframe.1,hframe.2.1,hframe.2.2.1,?_⟩
  · intro r
    rw [hstable _ (hskip r) (hcount r)]
    exact hh₁ r
  · simp [F,unaryCopiesR,hne,hspec.1,hframe.2.2.2 skip hskip]
  · simp [F,unaryCopiesR,hne.symm,hspec.2,hframe.2.2.2 count hcount]
  · intro k hr hk hk'
    exact (hstable k hk hk').trans (hframe.2.2.2 k hr)


theorem counterProgram_native (rg : TblR 9 → Fin T) (last : Bool) (skip count : Fin T) :
    mnNativePushBound 3 (counterProgram (P := P) (Q := Q) (A := A) (U := U) rg last skip count) :=
  ⟨tblCompile_native _ _,tblUnaryCopies_native _ _⟩

/-- The same charged trace has a stock bound linear in its time bill. -/
theorem counterProgram_within (rg : TblR 9 → Fin T) (last : Bool) (skip count : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n bill depth : ℕ)
    (he : Exec body (counterProgram rg last skip count) (mk v S) n (mk v' F))
    (hn : n ≤ bill) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*bill) depth
      (counterProgram rg last skip count) (mk v S) n (mk v' F) :=
  mn_native_exec_within he 3 (counterProgram_native rg last skip count) depth _
    (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.BoundaryCropMetadata
