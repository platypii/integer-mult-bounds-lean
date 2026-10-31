module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairBitPlanes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedKeyDescriptorInput
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Install descriptor headers and a live exposed payload around a numerical
bank. Ambient source exposure is deliberately a separate execution obligation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def descriptorHeaderPort (i : Fin 4) : Fin 276 := ⟨264+i.val,by omega⟩

theorem descriptorHeaderPort_injective : Function.Injective descriptorHeaderPort := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  change 264+i.val = 264+j.val at hv
  omega

def descriptorHeaderCopies (work : Fin 276 → Fin T) (source : Fin 4 → Fin T) : List (Fin T × Fin T) :=
  List.ofFn (fun i => (source i,work (descriptorHeaderPort i)))

def generateDescriptorFrame (work : Fin 276 → Fin T) (source : Fin 4 → Fin T)
    (payload tmp saved : Fin T) : Pr P T Q A U :=
  .seq (copyUnaryHeaders saved (descriptorHeaderCopies work source))
    (copyMappedWords payload (work 263) tmp saved id)

private theorem copies_native (tmp : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 2 (copyUnaryHeaders (P := P) (Q := Q) (A := A) (U := U) tmp rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush],ih⟩

theorem generateDescriptorFrame_exec (work : Fin 276 → Fin T) (hwork : Function.Injective work)
    (source : Fin 4 → Fin T) (payload tmp saved : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceSaved : ∀ i, source i ≠ saved)
    (hsavedOff : ∀ i, saved ≠ work i) (htmpOff : ∀ i, tmp ≠ work i)
    (hcopy : [payload,work 263,tmp,saved].Nodup) (hpayloadOff : ∀ i, payload ≠ work i)
    (p W N packet : ℕ) (xs : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A) (M : Stacks 263 A)
    (hview : embStk work S = extendStacks (by decide : 263 ≤ 276) M)
    (hvalues : ∀ i, (S.R (source i)).length = ![N,W,p,packet] i)
    (hpayload : S.R payload = xs) (htmp : S.R tmp = []) (hsaved : S.R saved = []) (depth : ℕ) :
    let rs := descriptorHeaderCopies work source
    let value := fun i => (S.R i).length
    let H := {S with R := unaryCopiesR value S.R rs}
    let F := {H with R := Function.update H.R (work 263) xs}
    ∃ v', v'.user = v.user ∧ embStk work F = packedKeyDescriptorInput M p W N packet xs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*copyUnaryHeadersCost value rs+2*(6*xs.length+6))) depth
        (generateDescriptorFrame work source payload tmp saved) (mk v S)
        (copyUnaryHeadersCost value rs+(6*xs.length+6)) (mk v' F) := by
  dsimp only
  let rs := descriptorHeaderCopies work source
  let value := fun i => (S.R i).length
  let H : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  have hregs : ∀ r ∈ rs, [r.1,r.2,saved].Nodup := by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨hsourceOff i _,hsourceSaved i⟩,(hsavedOff _).symm,⟨not_false,List.nodup_nil⟩⟩
  obtain ⟨v₁,hu₁,he₁⟩ := copyUnaryHeaders_exec (body := body) saved rs hregs (by
    intro r hr q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact (hsourceOff j _).symm) value v S (by intro r hr; rfl) hsaved
  have hoff (i : Fin T) (hi : ∀ j, i ≠ work (descriptorHeaderPort j)) : H.R i = S.R i := by
    apply unaryCopiesR_off
    intro r hr he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi j he.symm
  have h263 : H.R (work 263) = [] := by
    rw [hoff _ (by
      intro i he
      have hv := congrArg Fin.val (hwork he)
      change 263 = 264+i.val at hv
      omega)]
    have hv := congrArg (fun C : Stacks 276 A => C.R 263) hview
    exact hv.trans (extendStacks_fresh (by decide : 263 ≤ 276) M 263 (by decide)).2
  obtain ⟨v₂,hu₂,he₂⟩ := copyMappedWords_exec (body := body) payload (work 263) tmp saved hcopy id v₁ H
    (by rw [hoff _ (fun j => htmpOff _)]; exact htmp)
    (by rw [hoff _ (fun j => hsavedOff _)]; exact hsaved)
  rw [hoff payload (fun j => hpayloadOff _),hpayload,h263,List.map_id,List.append_nil] at he₂
  have hw₁ := mn_native_exec_within he₁ 2 (copies_native saved rs) depth _ (le_refl _)
  have hw₂ := mn_native_exec_within he₂ 2 (by
    simp [copyMappedWords,copyR,copyStep,moveR,whileR,moveStep,peekR,mnNativePushBound,mnActPush]) depth _ (le_refl _)
  refine ⟨v₂,hu₂.trans hu₁,?_,mn_seq_within_add hw₁ hw₂⟩
  have hnd : (rs.map Prod.snd).Nodup := by
    simp only [rs,descriptorHeaderCopies,List.map_ofFn,Function.comp_def]
    exact List.nodup_ofFn_ofInjective (hwork.comp descriptorHeaderPort_injective)
  have hbase (i : Fin 276) : S.R (work i) = (extendStacks (by decide : 263 ≤ 276) M).R i :=
    congrArg (fun C : Stacks 276 A => C.R i) hview
  refine Stacks.ext ?_ ?_ ?_ ?_
  · change S.inp = M.inp
    exact congrArg (fun C : Stacks 276 A => C.inp) hview
  · change S.out = M.out
    exact congrArg (fun C : Stacks 276 A => C.out) hview
  · funext i
    change S.L (work i) = (extendStacks (by decide : 263 ≤ 276) M).L i
    exact congrArg (fun C : Stacks 276 A => C.L i) hview
  · funext k
    by_cases hk : k = 263
    · subst k; simp [embStk,packedKeyDescriptorInput]
    have hu : work k ≠ work 263 := hwork.ne hk
    change Function.update H.R (work 263) xs (work k) = _
    rw [Function.update_of_ne hu]
    by_cases hh : ∃ i, descriptorHeaderPort i = k
    · obtain ⟨i,rfl⟩ := hh
      have hat := unaryCopiesR_at value S.R rs hnd (source i,work (descriptorHeaderPort i))
        (List.mem_ofFn.mpr ⟨i,rfl⟩)
      change unaryCopiesR value S.R rs (work (descriptorHeaderPort i)) = _
      rw [hat,hbase]
      simp only [value,hvalues]
      fin_cases i <;> simp [packedKeyDescriptorInput,descriptorHeaderPort,extendStacks]
    · have hn (i : Fin 4) : descriptorHeaderPort i ≠ k := fun he => hh ⟨i,he⟩
      rw [hoff _ (fun i he => hn i (hwork he).symm),hbase]
      have hv (i : Fin 4) : k.val ≠ 264+i.val := by
        intro he
        exact hn i (Fin.ext he.symm)
      have h264 : k.val ≠ 264 := by simpa using hv 0
      have h265 : k.val ≠ 265 := by simpa using hv 1
      have h266 : k.val ≠ 266 := by simpa using hv 2
      have h267 : k.val ≠ 267 := by simpa using hv 3
      have h263' : k.val ≠ 263 := by intro he; exact hk (Fin.ext he)
      simp only [packedKeyDescriptorInput,extendStacks]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
