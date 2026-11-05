module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSeamHeaderPreparation
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHeaderFrameRetirement

/-! Release the four generated caller headers after restoring publication.
Only the two consumer data ports remain changed from the original caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type}
noncomputable section

def seamTemporaryHeaders (T : ℕ) : List (Fin (MachineTapes T)) :=
  [fullHeader T (.publication 0),fullHeader T (.publication 1),
    fullHeader T (.publication 2),fullHeader T (.publication 3)]

def seamHeadersRetirement : Pr P (MachineTapes T) Q A U := clearWords (seamTemporaryHeaders T)

def seamHeadersRetireCost (p s width : ℕ) : ℕ :=
  2*((coreLength s width (boundaryCropIndex s width 0)+coreLength s width (boundaryCropIndex s width 1)+
    coreLength s width (boundaryCropIndex s width 2)+1)*(2*p+13))+9

theorem seamHeadersRetirement_exec (body : P → Pr P (MachineTapes T) Q A U)
    (p s width : ℕ) (v : HS (MachineTapes T) Q A U) (S : Stacks (MachineTapes T) A)
    (hblank : ∀ i : Fin 4, S.R (fullHeader T (.publication (Fin.castAdd 3 i))) = [])
    (src dst : Fin (MachineTapes T))
    (hsrc : ∀ i : Fin 4, src ≠ fullHeader T (.publication (Fin.castAdd 3 i)))
    (hdst : ∀ i : Fin 4, dst ≠ fullHeader T (.publication (Fin.castAdd 3 i)))
    (xs ys : List (Fin (A+4))) (depth : ℕ) :
    let M := seamHeadersState p s width S
    let F : Stacks (MachineTapes T) A := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        seamHeadersRetirement (mk v F) (seamHeadersRetireCost p s width)
        (mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  dsimp only
  have hnd : (seamTemporaryHeaders T).Nodup :=
    (show ([Role.publication 0,.publication 1,.publication 2,.publication 3] : List Role).Nodup by decide).map
      (fullHeader_injective T)
  have hsrc' : src ∉ seamTemporaryHeaders T := by
    simp only [seamTemporaryHeaders,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hsrc 0,hsrc 1,hsrc 2,hsrc 3⟩
  have hdst' : dst ∉ seamTemporaryHeaders T := by
    simp only [seamTemporaryHeaders,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hdst 0,hdst 1,hdst 2,hdst 3⟩
  have hf (i : Fin (MachineTapes T)) (hi : i ∉ seamTemporaryHeaders T) :
      (seamHeadersState p s width S).R i = S.R i := by
    apply seamHeadersState_off p s width S i
    intro j hj
    apply hi
    fin_cases j <;> simp [seamTemporaryHeaders, hj]
  have hb : ∀ i ∈ seamTemporaryHeaders T, S.R i = [] := by
    intro i hi
    simp only [seamTemporaryHeaders,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hblank 0
    · exact hblank 1
    · exact hblank 2
    · exact hblank 3
  obtain ⟨v',hu,he⟩ := retireHeaderFrame_pair_exec body (seamTemporaryHeaders T) hnd S
    (seamHeadersState p s width S) rfl rfl rfl hf hb src dst hsrc' hdst' xs ys v depth
  have hcost : (2*((seamTemporaryHeaders T).map
      (fun i => ((seamHeadersState p s width S).R i).length)).sum+2*(seamTemporaryHeaders T).length+1) =
      seamHeadersRetireCost p s width := by
    have h0 : ((seamHeadersState p s width S).R (fullHeader T (.publication 0))).length =
        coreLength s width (boundaryCropIndex s width 0)*(2*p+13) := seamHeadersState_counts p s width S 0
    have h1 : ((seamHeadersState p s width S).R (fullHeader T (.publication 1))).length =
        coreLength s width (boundaryCropIndex s width 1)*(2*p+13) := seamHeadersState_counts p s width S 1
    have h2 : ((seamHeadersState p s width S).R (fullHeader T (.publication 2))).length =
        coreLength s width (boundaryCropIndex s width 2)*(2*p+13) := seamHeadersState_counts p s width S 2
    have h3 := seamHeadersState_narrow p s width S
    simp only [seamTemporaryHeaders,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil]
    change 2*(((seamHeadersState p s width S).R (fullHeader T (.publication 0))).length+
      (((seamHeadersState p s width S).R (fullHeader T (.publication 1))).length+
      (((seamHeadersState p s width S).R (fullHeader T (.publication 2))).length+
      (((seamHeadersState p s width S).R (fullHeader T (.publication 3))).length+0))))+2*4+1 = _
    rw [h0,h1,h2,h3]
    unfold seamHeadersRetireCost
    simp only [Nat.add_mul,Nat.one_mul]
    omega
  rw [hcost] at he
  exact ⟨v',hu,he⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.CallerLayout
