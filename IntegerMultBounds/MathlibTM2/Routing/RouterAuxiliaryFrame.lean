module

public import IntegerMultBounds.MathlibTM2.Routing.RouterAuxiliaryGenerate
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankCopy
public import IntegerMultBounds.MathlibTM2.Routing.DelimitedBankTrace

/-! Separate serializers for the seven live-profile and six width operands.
They can be inserted on either side of the header bank in full-frame order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerAuxiliaryFrameSources (profile : Bool) : List (Fin 12) :=
  if profile then (List.finRange 7).map routerAuxiliaryProfileSource
  else (List.finRange 6).map routerAuxiliaryWidthSource

def routerAuxiliaryFrameWord (W n wy : ℕ) (i : Fin 12) : List (Fin (A+4)) :=
  if i = 3 then binSyms W n else if i = 4 then binSyms (canonicalScalarWidth wy) wy
  else if i = 5 then [bitSymbol true] else []

theorem routerAuxiliaryFrameSources_mem (profile : Bool) (i : Fin 12)
    (hi : i ∈ routerAuxiliaryFrameSources profile) : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
  cases profile <;> simp [routerAuxiliaryFrameSources,List.finRange_succ,
    routerAuxiliaryProfileSource,routerAuxiliaryWidthSource] at hi <;> tauto

theorem routerAuxiliaryBank_frameWord (R : Fin T → List (Fin (A+4)))
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (W n wy : ℕ)
    (hblank : R (rg 6) = []) (profile : Bool) (i : Fin 12)
    (hi : i ∈ routerAuxiliaryFrameSources profile) :
    routerAuxiliaryBank R rg W n wy (rg i) = routerAuxiliaryFrameWord W n wy i := by
  rcases routerAuxiliaryFrameSources_mem profile i hi with rfl | rfl | rfl | rfl <;>
    simp [routerAuxiliaryBank,routerAuxiliaryFrameWord,hrg.eq_iff,hblank]

def routerAuxiliaryFrameJobs (rg : Fin 12 → Fin T) (profile : Bool) (W n wy : ℕ) :=
  (routerAuxiliaryFrameSources profile).map (fun i => (rg i,routerAuxiliaryFrameWord (A := A) W n wy i))

def routerAuxiliaryFrame (delimiter : Fin (A+4)) (rg : Fin 12 → Fin T)
    (profile : Bool) (W n wy : ℕ) :=
  delimitedBankFrames delimiter (routerAuxiliaryFrameJobs rg profile W n wy)

def routerAuxiliaryCopyProgram (rg : Fin 12 → Fin T) (dst : Fin T)
    (delimiter : Fin (A+4)) (profile : Bool) : Pr P T Q A U :=
  delimitedBankCopy dst (rg 9) (rg 10) delimiter ((routerAuxiliaryFrameSources profile).map rg)

theorem routerAuxiliaryCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (dst : Fin T)
    (hoff : ∀ i, rg i ≠ dst) (delimiter : Fin (A+4)) (profile : Bool) (W n wy : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hbank : ∀ i ∈ routerAuxiliaryFrameSources profile, S.R (rg i) = routerAuxiliaryFrameWord W n wy i)
    (htmp : S.R (rg 9) = []) (hwork : S.R (rg 10) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 7*(6*(W+canonicalScalarWidth wy+1)+7)+1 ∧
      Exec body (routerAuxiliaryCopyProgram rg dst delimiter profile) (mk v S) m
        (mk v' { S with R := (Function.update S.R dst
          (routerAuxiliaryFrame delimiter rg profile W n wy ++ S.R dst)) }) := by
  obtain ⟨v',hu,he⟩ := delimitedBankCopy_exec body dst (rg 9) (rg 10)
    (by simp [List.nodup_cons,(hoff 9).symm,(hoff 10).symm,hrg.eq_iff]) delimiter
    (routerAuxiliaryFrameJobs rg profile W n wy) (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
      have hs := routerAuxiliaryFrameSources_mem profile i hi
      exact ⟨hoff _,hrg.ne (by rcases hs with rfl | rfl | rfl | rfl <;> decide),
        hrg.ne (by rcases hs with rfl | rfl | rfl | rfl <;> decide)⟩) v S
    (by intro j hj; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj; exact hbank i hi) htmp hwork
  have hl : (routerAuxiliaryFrameJobs (A := A) rg profile W n wy).length ≤ 7 := by
    cases profile <;> simp [routerAuxiliaryFrameJobs,routerAuxiliaryFrameSources]
  have hf := delimitedBankFrames_length_le delimiter (routerAuxiliaryFrameJobs rg profile W n wy)
    (W+canonicalScalarWidth wy+1) (by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hj
      rcases routerAuxiliaryFrameSources_mem profile i hi with rfl | rfl | rfl | rfl <;>
        simp [routerAuxiliaryFrameWord,length_binSyms] <;> omega)
  have hc : delimitedBankCopyCost (routerAuxiliaryFrameJobs (A := A) rg profile W n wy) ≤
      7*(6*(W+canonicalScalarWidth wy+1)+7)+1 := by
    rw [delimitedBankCopyCost_eq delimiter]
    nlinarith only [hf,hl,Nat.mul_le_mul_right (W+canonicalScalarWidth wy+1) hl]
  refine ⟨v',_,hu,hc,?_⟩
  simpa only [routerAuxiliaryCopyProgram,routerAuxiliaryFrame,routerAuxiliaryFrameJobs,
    List.map_map,Function.comp_def] using he

end IntegerMultBounds.MathlibTM2.Routing
