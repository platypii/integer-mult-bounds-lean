module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyComplexBatchStep
public import IntegerMultBounds.MathlibTM2.StackResources
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundaryBatch

/-! The live family batch retains its input and accumulates one output per line.
Retained pages and all spectator stacks are included in the initial stock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {U : Type}

theorem mnSize_mk_updateR (v : HS T Q A U) (S : Stacks T A) (i : Fin T)
    (xs : List (Fin (A+4))) :
    mnSize (mk v {S with R := Function.update S.R i xs})+(S.R i).length =
      mnSize (mk v S)+xs.length := by
  simpa only [mk,update_rt,get_rt] using
    mn_size_update (mk v S) v (.rt i) xs

/-- Parking moves the input into its saved stream and adds exactly one output. -/
theorem familyComplexBatchNext_stock (v v' : HS 263 Q A U) (S : Stacks 263 A)
    (input output tail : List (Fin (A+4))) (hsource : S.R 110 = input++tail) :
    mnSize (mk v' (familyComplexBatchNext S input output tail)) =
      mnSize (mk v S)+output.length := by
  have h₁ := mnSize_mk_updateR v S 110 tail
  let S₁ : Stacks 263 A := {S with R := Function.update S.R 110 tail}
  have h₂ := mnSize_mk_updateR v S₁ 241 (input.reverse++S.R 241)
  let S₂ : Stacks 263 A := {S₁ with R := Function.update S₁.R 241 (input.reverse++S.R 241)}
  have h₃ := mnSize_mk_updateR v S₂ 242 (output.reverse++S.R 242)
  simp only [S₁,S₂,Function.update_of_ne (by decide : (241 : Fin 263) ≠ 110),
    Function.update_of_ne (by decide : (242 : Fin 263) ≠ 241),
    Function.update_of_ne (by decide : (242 : Fin 263) ≠ 110),
    List.length_append,List.length_reverse] at h₂ h₃
  have hinput : (S.R 110).length = input.length+tail.length := by simp [hsource]
  change mnSize (mk v {S with R := Function.update (Function.update (Function.update S.R 110 tail)
    241 (input.reverse++S.R 241)) 242 (output.reverse++S.R 242)}) = _
  omega

/-- Stock at an iteration boundary includes input tails, saved inputs, produced
outputs, the count, every retained page and every spectator stack simultaneously. -/
theorem familyComplexBatch_stock_le (v v' : HS 263 Q A U) (S R : Stacks 263 A) (B : ℕ)
    (hi : R.inp = S.inp) (ho : R.out = S.out) (hL : R.L = S.L)
    (hframe : ∀ k, k ∉ ([110,240,241,242] : List (Fin 263)) → R.R k = S.R k)
    (hsource : (R.R 110).length+(R.R 241).length ≤ (S.R 110).length+(S.R 241).length)
    (hcount : (R.R 240).length ≤ (S.R 240).length)
    (houtput : (R.R 242).length ≤ (S.R 242).length+B) :
    mnSize (mk v' R) ≤ mnSize (mk v S)+B := by
  let S₁ : Stacks 263 A := {S with R := Function.update S.R 110 (R.R 110)}
  let S₂ : Stacks 263 A := {S₁ with R := Function.update S₁.R 240 (R.R 240)}
  let S₃ : Stacks 263 A := {S₂ with R := Function.update S₂.R 241 (R.R 241)}
  let S₄ : Stacks 263 A := {S₃ with R := Function.update S₃.R 242 (R.R 242)}
  have he : R = S₄ := by
    refine Stacks.ext hi ho hL ?_
    funext k
    by_cases h110 : k = 110
    · subst k; simp [S₄,S₃,S₂,S₁]
    by_cases h240 : k = 240
    · subst k; simp [S₄,S₃,S₂,S₁]
    by_cases h241 : k = 241
    · subst k; simp [S₄,S₃,S₂,S₁]
    by_cases h242 : k = 242
    · subst k; simp [S₄,S₃,S₂,S₁]
    simpa [S₄,S₃,S₂,S₁,h110,h240,h241,h242] using
      hframe k (by simp [h110,h240,h241,h242])
  have h₁ := mnSize_mk_updateR v S 110 (R.R 110)
  have h₂ := mnSize_mk_updateR v S₁ 240 (R.R 240)
  have h₃ := mnSize_mk_updateR v S₂ 241 (R.R 241)
  have h₄ := mnSize_mk_updateR v S₃ 242 (R.R 242)
  have hc : S₁.R 240 = S.R 240 := by rfl
  have ha : S₂.R 241 = S.R 241 := by rfl
  have hb : S₃.R 242 = S.R 242 := by rfl
  rw [hc] at h₂
  rw [ha] at h₃
  rw [hb] at h₄
  change mnSize (mk v S₁)+(S.R 110).length = _ at h₁
  change mnSize (mk v S₂)+(S.R 240).length = _ at h₂
  change mnSize (mk v S₃)+(S.R 241).length = _ at h₃
  change mnSize (mk v S₄)+(S.R 242).length = _ at h₄
  rw [he]
  change mnSize (mk v S₄) ≤ _
  omega

noncomputable def familyComplexBatchStepCost (A p u l s t a b target : ℕ) [NeZero s] : ℕ :=
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloBoundary s t
      (IntegerMultBounds.NLogN.PhaseCellBand.width p u) a b).card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  originalComponentInputsCost q s+
    familyBoundaryPairCost A p u l s t a b target
      (publicationGeometryWidth t (IntegerMultBounds.NLogN.PhaseCellBand.width p u))+
    (8*(s*w)+8)

theorem familyBatchWords_length {s : ℕ} (w : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    (cstream A w (Fs.map (chirpLine s)).flatten).length = Fs.length*s*w := by
  simpa only [List.length_map] using cstream_flatten_length (A := A) w s
    (Fs.map (chirpLine s)) (by
      intro xs hxs
      obtain ⟨F,_,rfl⟩ := List.mem_map.mp hxs
      simp [chirpLine])

/-- The actual source/saved/output streams of the family loop cost at most one
extra batch of output words, uniformly over the iteration index. -/
theorem familyComplexBatchPrefix_stock_le {s : ℕ} (v v' : HS 263 Q A U)
    (S R : Stacks 263 A) (w j : ℕ) (Fs Zs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (hj : j ≤ Fs.length) (hZs : Zs.length ≤ Fs.length)
    (hi : R.inp = S.inp) (ho : R.out = S.out) (hL : R.L = S.L)
    (hframe : ∀ k, k ∉ ([110,240,241,242] : List (Fin 263)) → R.R k = S.R k)
    (hSsource : S.R 110 = cstream A w (Fs.map (chirpLine s)).flatten++tail)
    (hSsaved : S.R 241 = []) (hSoutput : S.R 242 = [])
    (hsource : R.R 110 = cstream A w ((Fs.drop j).map (chirpLine s)).flatten++tail)
    (hsaved : R.R 241 = (cstream A w ((Fs.take j).map (chirpLine s)).flatten).reverse)
    (houtput : R.R 242 = (cstream A w (Zs.map (chirpLine s)).flatten).reverse)
    (hcount : (R.R 240).length ≤ (S.R 240).length) :
    mnSize (mk v' R) ≤ mnSize (mk v S)+Fs.length*s*w := by
  apply familyComplexBatch_stock_le v v' S R _ hi ho hL hframe ?_ hcount ?_
  · rw [hsource,hsaved,hSsource,hSsaved]
    simp only [List.length_append,List.length_reverse,List.length_nil,familyBatchWords_length,
      List.length_drop,List.length_take,Nat.min_eq_left hj,Nat.add_zero]
    have hsplit : Fs.length-j+j = Fs.length := Nat.sub_add_cancel hj
    nlinarith only [congrArg (fun n => n*s*w) hsplit]
  · rw [houtput,hSoutput]
    simp only [List.length_reverse,List.length_nil,familyBatchWords_length,Nat.zero_add]
    exact Nat.mul_le_mul_right w (Nat.mul_le_mul_right s hZs)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
