module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapDimensions
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafReturnHeaders

/-! Generate the two equal field-volume factors and trailing width of the record payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host

theorem recordVolumeHeaders_exec {T Q A : ℕ} {F U : Type}
    (body : F → Pr F T Q A U) (r : Fin 10 ↪ Fin T) (width : Fin T) (outside : ∀ i, width ≠ r i)
    (d H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (u : HS T Q A U) (S : Stacks T A)
    (base : S.R (r 0) = binSyms H M) (one : S.R (r 1) = binSyms 1 1)
    (trailing : S.R width = binSyms J W) (free : ∀ i : Fin 10, 2 ≤ i → S.R (r i) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) ∧
      Exec body ((swapPrefix r d).seq (Routing.binaryCanonicalCopyProgram width (r 9) (r 3) (r 4)))
        (mk u S) n (mk z {S with R := Function.update (Function.update S.R (r 2) (binSyms (M^d).size (M^d))) (r 9) (binSyms W.size W)}) := by
  have canonical (a : ℕ) : (FlatCoordinateSchedule.bits a).map (bitSymbol (a := A)) = binSyms a.size a := by
    rw [binSyms_eq]
    congr 1
    exact BinaryCanonicalData.value_injective _ _ (FlatCoordinateSchedule.bits_canonical _)
      (Mult.PhaseCellToeplitz.binBits_size_canonical _) ((FlatCoordinateSchedule.bits_value _).trans
        (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _)).symm)
  obtain ⟨v,t,user,time,power⟩ := swapPrefix_exec body r d H M hm u S base one (fun i hi _ => free i hi)
  let D : Stacks T A := {S with R := Function.update S.R (r 2) ((FlatCoordinateSchedule.bits (M^d)).map bitSymbol)}
  have ports : [width,r 9,r 3,r 4].Nodup := by simp [outside,r.injective.eq_iff]
  obtain ⟨z,hz,copy⟩ := swapWidth_exec body width (r 9) (r 3) (r 4) ports J W hw v D
    (by simp [D,outside,trailing]) (by simp [D,r.injective.eq_iff,free])
    (by simp [D,r.injective.eq_iff,free]) (by simp [D,r.injective.eq_iff,free])
  refine ⟨z,_,hz.trans user,Nat.add_le_add_right time _,?_⟩
  simpa only [D,canonical] using Exec.seq power copy

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
theorem recordPayloadReturn_exec {T Q : ℕ} {F U : Type} (capacity : 217 ≤ Q)
    (body : F → Pr F T Q prime U) (dim ret : Fin 10 ↪ Fin T) (width : Fin T)
    (outside : ∀ i, width ≠ dim i) (apart : ∀ j, dim 2 ≠ ret j ∧ dim 9 ≠ ret j)
    (d H J M W : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hM : 0 < M) (hW : 0 < W)
    (u : HS T Q prime U) (S : Stacks T prime) (base : S.R (dim 0) = binSyms H M)
    (one : S.R (dim 1) = binSyms 1 1) (trailing : S.R width = binSyms J W)
    (free : ∀ i : Fin 10, 2 ≤ i → S.R (dim i) = [])
    (empty : ∀ i : Fin 10, 2 ≤ i.val → S.L (ret i) = [] ∧ S.R (ret i) = [])
    (source : ℤ → Fin 4) (p : ℤ) (xs : List (ZMod 2)) (length : xs.length = M^(d+d)*W)
    (dst : ∀ z, readAt blank (S.L (ret 0)) (S.R (ret 0)) z = leafBitTape xs z)
    (src : ∀ z, readAt blank (S.L (ret 1)) (S.R (ret 1)) (z-p) = RadixToBinary.binaryEncoding.encode (source z)) :
    let generate := (swapPrefix dim d).seq (Routing.binaryCanonicalCopyProgram width (dim 9) (dim 3) (dim 4))
    let header : Fin 3 → Fin T := ![dim 9,dim 2,dim 2]
    let ports := (Fin.castAddEmb (n := 8) 2).trans ret
    let setup := Record.copyLeafHeaders header (returnHeaderTargets.trans ret) (ret 8) (ret 9) (List.finRange 3)
    let localRun : Pr Empty 8 217 prime U := (.act (pushMarkers [2,3,4,5,6,7]) : Pr Empty 8 217 prime U).seq
      (returnFromOrigin (Function.Embedding.refl _))
    let finish := setup.seq (statePlacedNormalized ports capacity (by decide) Empty.elim localRun)
    ∃ z D n, z.user = u.user ∧ n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) +
      (6*(W.size+(M^d).size+(M^d).size)+19+((218*xs.length+1)*13+8)) ∧
      Exec body (generate.seq finish) (mk u S) n (mk z D) ∧
      (∀ z, readAt blank (D.L (ret 1)) (D.R (ret 1)) (z-p) =
        RadixToBinary.binaryEncoding.encode (putWord source p (xs.map SparseRoleCircuit.encode) z)) ∧
      ∀ j, dim 2 ≠ j → dim 9 ≠ j → (∀ i, ret i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro generate header ports setup localRun finish
  obtain ⟨y,t,hy,ht,run⟩ := recordVolumeHeaders_exec body dim width outside d H J M W hm hw u S base one trailing free
  let E : Stacks T prime := {S with R := Function.update (Function.update S.R (dim 2) (binSyms (M^d).size (M^d))) (dim 9) (binSyms W.size W)}
  have keep (j) (a : dim 2 ≠ j) (b : dim 9 ≠ j) : E.R j = S.R j := by simp [E,a.symm,b.symm]
  have len : xs.length = M^d*(M^d*W) := by rw [length,pow_add,Nat.mul_assoc]
  have disjoint (i : Fin 3) (j : Fin 10) : header i ≠ ret j := by
    fin_cases i <;> first | exact (apart j).2 | exact (apart j).1
  obtain ⟨z,D,n,hz,hn,retRun,read,frame⟩ := stagedLeafReturn_exec (pow_pos hM d) (pow_pos hM d) hW
    capacity body ret header disjoint y E source p xs len
    (by intro z; rw [keep _ (apart 0).1 (apart 0).2]; exact dst z)
    (by intro z; rw [keep _ (apart 1).1 (apart 1).2]; exact src z)
    (by intro i; fin_cases i <;> simp [E,header,dim.injective.eq_iff])
    (by intro i hi; rw [keep _ (apart i).1 (apart i).2]; exact empty i hi)
  refine ⟨z,D,_,hz.trans hy,?_,Exec.seq run retRun,read,?_⟩
  · rw [len]; exact Nat.add_le_add ht hn
  · intro j a b off
    exact ⟨(frame j off).1,(frame j off).2.trans (keep j a b)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
