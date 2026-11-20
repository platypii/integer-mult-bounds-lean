module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel
public import IntegerMultBounds.MathlibTM2.Cover.LabelPadProgram
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup

/-! Generate both selector streams for the classified scan on shared residue counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem recordMasks_exec {T Q A m r : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (hr : r ≤ m) (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = m*m) (mask mode parents saved : Fin T)
    (apart : mask ≠ mode) (maskRegs : (parents :: saved :: (slots rs ++ [mask])).Nodup)
    (modeRegs : (parents :: saved :: (slots rs ++ [mode])).Nodup) :
    ∃ program : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ)
      (proj : LabelPadding.Label m (w+1)), (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request →
      v.beforeH = B*prime^(m*((w+1)*m)) →
      ∀ (u : HS T Q A U) (S : Stacks T A), ready (prime^w) S.R rs → S.R saved = [] →
      (S.R parents).length = v.beforeRows*v.rows*B → S.R mask = [] → S.R mode = [] →
      let labels := List.range (LabelMask.records v)
      let live := labels.map fun i => bitSymbol (a := A) (LabelStock.live m (w+1) 1 i)
      let bad := labels.map fun i => bitSymbol (a := A) (fallbackBit hr proj (physicalLabel m (w+1) i))
      ∃ z n, z.user = u.user ∧ n ≤ 2*((6+10*(m*m))*labels.length+4) ∧
        Exec body program (mk u S) n (mk z {S with R := Function.update (Function.update S.R mask live) mode bad}) := by
  obtain ⟨writeLive,hl⟩ := record_writes (body := body) m rs size mask parents saved maskRegs
  obtain ⟨writeBad,hb⟩ := fallbackMask_writes body r hr request rs size mode parents saved modeRegs
  refine ⟨writeLive.seq writeBad,?_⟩
  intro v w B proj reduction shape u S radix scratch count freeMask freeMode labels live bad
  obtain ⟨y,n,hy,hn,emit⟩ := hl v (w+1) B (by omega) shape u S ⟨radix,scratch,count⟩
  simp only [freeMask,List.append_nil,LabelMask.selectors,List.map_map,Function.comp_def] at emit
  let R := Function.update S.R mask live
  have hp := (List.nodup_cons.mp maskRegs).1
  have hs := (List.nodup_cons.mp (List.nodup_cons.mp maskRegs).2).1
  have sep := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp maskRegs).2).2).2.2
  have keep (k : Fin T) (hk : k ∈ slots rs) : R k = S.R k :=
    Function.update_of_ne (sep k hk mask (by simp)) _ _
  have radix' : ready (prime^w) R rs := by
    intro pair h
    rw [keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩),keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩)]
    exact radix pair h
  have savedOff : saved ≠ mask := by rintro rfl; exact hs (by simp)
  have parentsOff : parents ≠ mask := by rintro rfl; exact hp (by simp)
  obtain ⟨z,t,hz,ht,emitBad⟩ := hb v w B proj reduction shape y {S with R := R}
    ⟨radix',(Function.update_of_ne savedOff ..).trans scratch,by simpa [R,parentsOff] using count⟩
  have empty : R mode = [] := (Function.update_of_ne apart.symm live S.R).trans freeMode
  simp only [empty,List.append_nil,List.map_map,Function.comp_def] at emitBad
  have bill := LabelPadProgram.selector_cost v m (w+1) B (by omega) shape
  simp only [Nat.add_sub_cancel] at bill hn
  refine ⟨z,n+t,hz.trans hy,?_,Exec.seq emit emitBad⟩
  simp only [labels,List.length_range]
  omega

/-- Clear the traversal workspace before the record loop borrows it. The two
generated words are the only changes to the cleaned bank. -/
theorem clearAfterMasks_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (mask mode : Fin T) (is : List (Fin T)) (unique : is.Nodup) (hm : mask ∉ is) (hb : mode ∉ is)
    (live bad : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A) :
    let setBits := fun (D : Stacks T A) => {D with R := Function.update (Function.update D.R mask live) mode bad}
    let clean := {S with L := fun i => if i ∈ is then [] else S.L i,
                         R := fun i => if i ∈ is then [] else S.R i}
    ∃ z, z.user = u.user ∧ Exec body (clearWorkTapes is) (mk u (setBits S))
      ((is.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1) (mk z (setBits clean)) := by
  intro setBits clean
  obtain ⟨z,user,run⟩ := clearWorkTapes_exec body is unique u (setBits S)
  have frame (i) (h : i ∈ is) : (setBits S).R i = S.R i := by
    have m : i ≠ mask := fun eq => hm (eq ▸ h)
    have b : i ≠ mode := fun eq => hb (eq ▸ h)
    simp [setBits,Function.update_of_ne,m,b]
  have cost := List.map_congr_left (l := is) (fun i hi => congrArg
    (fun xs : List (Fin (A+4)) => 4*(S.L i).length+2*xs.length+4) (frame i hi))
  rw [cost] at run
  refine ⟨z,user,?_⟩
  convert run using 2
  apply Stacks.ext <;> try rfl
  funext i
  by_cases h : i ∈ is
  · have m : i ≠ mask := fun eq => hm (eq ▸ h)
    have b : i ≠ mode := fun eq => hb (eq ▸ h)
    simp [setBits,clean,h,m,b]
  · by_cases b : i = mode
    · subst i; simp [setBits,clean,hb]
    · simp only [setBits,Function.update_of_ne b,clean,ite_eq_right h]
      by_cases m : i = mask <;> simp [m,h]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
