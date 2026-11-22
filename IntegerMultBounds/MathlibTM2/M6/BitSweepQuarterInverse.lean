module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepIntegerEntry
public import IntegerMultBounds.MathlibTM2.M6.PrefixMinor
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotInverse

/-! Prepare the shared inverse of four from the live PR589 modulus and clock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks Shared50ModularControl
open IntegerMultBounds.Machine Cover.Fallback RingFormula Host Stack Node Cover.LabelTraversal
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem sweepQuarterInverse_exec {P U : Type} {T Q D : ℕ} (body : P → Pr P T Q prime U)
    (pool : Fin ((D+1)*13) ↪ Fin T) (c : Fin 6 ↪ Fin T) (r : Fin 16 ↪ Fin T)
    (outside : ∀ i j, c i ≠ pool j) (pivotOff : ∀ i, c i ≠ r 14)
    (depth : (sweepIntFormula 4).depth ≤ D) (clock count : Fin T)
    (copyPorts : [clock,count,r 2,r 3].Nodup) (counterOff : ∀ i, r i ≠ count) (clockOff : clock ≠ r 14) :
    ∃ program : Pr P T Q prime U, ∀ w H (v : HS T Q prime U) (S : Stacks T prime),
    let M := prime^(w+1)
    let four := (4 : ZMod M)
    let C := 48*H*H+152*H+66
    let entry := (D+1)*(6*H+6)+1+(time H (fun _ => 6*H+6) (sweepIntFormula 4)+((D+1)*(2*H+2)+1))+(4*H+4)
    M < 2^H → (S.R clock).length = w → S.R count = [] → S.R (r 14) = [] →
    S.R (r 15) = binSyms H (1 : ZMod M).val → S.R (r 4) = binSyms H M →
    (∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (r i) = []) →
    S.R (c 0) = binSyms H 0 → S.R (c 1) = binSyms H (1 : ZMod M).val → S.R (c 2) = binSyms H M →
    (∀ i : Fin 6, 3 ≤ i → S.R (c i) = []) → (∀ j, S.R (pool j) = []) →
    ∃ z t, z.user = v.user ∧ t ≤ entry+(6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C)))+(2*H+2) ∧
      Exec body program (mk v S) t (mk z {S with R := Function.update S.R (r 0) (binSyms H (Ring.inverse four).val)}) := by
  let leaf : Leaf Empty → Fin T → Pr P T Q prime U := fun a dst => bcopy (literalSource c a) dst (c 4) (c 5)
  let emit : Pr P T Q prime U := .seq ((initFrames pool (c 2) (D+1)).seq
    ((compile leaf (registerBank pool) (sweepIntFormula 4) 0 (c 3)).seq (clearFrames pool (D+1))))
    (moveRightOrdered (c 3) (c 4) (r 14))
  refine ⟨.seq (.seq emit (reusablePivotInverse prime r clock count)) (bclear (r 14)),?_⟩
  intro w H v S M four C entry fits ticks counter pivot oneWord modWord free zero one modulus scratch blank
  have unit : IsUnit four := by simpa [four,M] using prefix_denominator_unit 4 (by decide) (by decide) (w+1)
  obtain ⟨u,k,hu,hk,write⟩ := sweepIntEntry_writes body pool c outside (r 14) pivotOff 4 depth H fits v S
    ⟨zero,one,modulus,scratch,blank⟩
  rw [pivot,List.append_nil] at write
  simp only [Int.cast_ofNat] at write
  let B := {S with R := Function.update S.R (r 14) (binSyms H four.val)}
  have keep (i) (hi : i ≠ r 14) : B.R i = S.R i := Function.update_of_ne hi _ _
  obtain ⟨y,F,l,hy,hl,run,_,inv,left,inp,out,frame⟩ := reusablePivotInverse_exec body prime w prime_prime four unit r
    clock count copyPorts counterOff H fits u B (by rwa [keep _ clockOff]) ((keep _ (counterOff 14).symm).trans counter)
    (Function.update_self ..) ((keep _ (r.injective.ne (by decide))).trans oneWord)
    ((keep _ (r.injective.ne (by decide))).trans modWord)
    (fun i hi hj => (keep _ (r.injective.ne (by omega))).trans (free i hi hj))
  have val := (frame (r 14) (r.injective.ne (by decide))).trans (Function.update_self ..)
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 14) y F
  have final : {F with R := Function.update F.R (r 14) []} =
      {S with R := Function.update S.R (r 0) (binSyms H (Ring.inverse four).val)} := by
    refine Stacks.ext inp out left ?_
    funext i
    by_cases h : i = r 14
    · subst i; simp [Function.update_of_ne (r.injective.ne (by decide : (14 : Fin 16) ≠ 0)),pivot]
    by_cases g : i = r 0
    · subst i; simpa [Function.update_of_ne h] using inv
    simpa [Function.update_of_ne h,Function.update_of_ne g] using (frame i g).trans (keep i h)
  rw [final,val,length_binSyms] at clear
  exact ⟨z,_,hz.trans (hy.trans hu),Nat.add_le_add_right (Nat.add_le_add hk hl) _,Exec.seq (Exec.seq write run) clear⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
