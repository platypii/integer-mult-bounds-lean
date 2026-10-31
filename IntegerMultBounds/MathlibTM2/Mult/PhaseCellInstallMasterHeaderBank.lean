module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMasterHeaderBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderCopies
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Install the numerical factory's ten ordinary masters from retained live
headers. The existing structural copier supplies execution and scratch reuse. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

private theorem copyUnaryHeaders_native (tmp : Fin T) (rs : List (Fin T × Fin T)) :
    mnNativePushBound 2 (copyUnaryHeaders (P := P₀) (Q := Q) (A := A) (U := U) tmp rs) := by
  induction rs with
  | nil => exact Nat.zero_le _
  | cons r rs ih =>
    exact ⟨by simp [ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush],ih⟩

def masterHeaderCopies (work : Fin 224 → Fin T) (source : Fin 10 → Fin T) : List (Fin T × Fin T) :=
  List.ofFn (fun i => (source i,work (inverseMasterCorePort i)))

theorem installMasterHeaderBank_exec (work : Fin 224 → Fin T) (hwork : Function.Injective work)
    (source : Fin 10 → Fin T) (tmp : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp)
    (P N q l s t u band a b : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = masterHeaderValues P N q l s t u band a b i)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = []) (htmp : S.R tmp = [])
    (depth : ℕ) :
    let rs := masterHeaderCopies work source
    let value := fun i => (S.R i).length
    let F := {S with R := unaryCopiesR value S.R rs}
    ∃ v', v'.user = v.user ∧
      embStk work F = {masterHeaderBank (masterHeaderValues P N q l s t u band a b) [] with inp := S.inp, out := S.out} ∧
      LengthKeyReady P N q l s t u band 0 0 []
        (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg
          (embStk boundaryFactorLegacyReg (embStk work F))))) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (mk v S)+depth+2*copyUnaryHeadersCost value rs)
        depth (copyUnaryHeaders tmp rs) (mk v S) (copyUnaryHeadersCost value rs) (mk v' F) := by
  dsimp only
  let rs := masterHeaderCopies work source
  let value := fun i => (S.R i).length
  let F : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  have hregs : ∀ r ∈ rs, [r.1,r.2,tmp].Nodup := by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨⟨hsourceOff i _,hsourceTmp i⟩,hworkTmp _,⟨not_false,List.nodup_nil⟩⟩
  obtain ⟨v',hu,he⟩ := copyUnaryHeaders_exec (body := body) tmp rs hregs
    (by
      intro r hr p hp
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
      exact (hsourceOff j _).symm)
    value v S (by intro r hr; rfl) htmp
  have hbank : embStk work F =
      {masterHeaderBank (masterHeaderValues P N q l s t u band a b) [] with inp := S.inp, out := S.out} := by
    have hnd : (rs.map Prod.snd).Nodup := by
      simp only [rs,masterHeaderCopies,List.map_ofFn,Function.comp_def]
      exact List.nodup_ofFn_ofInjective (hwork.comp inverseMasterCorePort_injective)
    refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      exact hleft i
    · funext j
      by_cases hm : ∃ i, inverseMasterCorePort i = j
      · obtain ⟨i,rfl⟩ := hm
        have hh := unaryCopiesR_at value S.R rs hnd (source i,work (inverseMasterCorePort i))
          (List.mem_ofFn.mpr ⟨i,rfl⟩)
        change unaryCopiesR value S.R rs (work (inverseMasterCorePort i)) = _
        rw [hh,hblank,List.append_nil]
        simpa only [value,hvalues] using (masterHeaderBank_headers
          (A := A) (masterHeaderValues P N q l s t u band a b) [] i).symm
      · have hoff : ∀ i, inverseMasterCorePort i ≠ j := by
          intro i hi
          exact hm ⟨i,hi⟩
        change unaryCopiesR value S.R rs (work j) = _
        rw [unaryCopiesR_off value S.R rs (work j) (by
          intro r hr he
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
          exact hoff i (hwork he)),hblank,masterHeaderBank_off _ [] j hoff]
        split_ifs <;> rfl
  refine ⟨v',hu,hbank,?_,mn_native_exec_within he 2 (copyUnaryHeaders_native tmp rs) depth _ (le_refl _)⟩
  rw [hbank]
  exact masterHeaderBank_ready P N q l s t u band a b [] S.inp S.out

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
