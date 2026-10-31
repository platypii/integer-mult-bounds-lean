module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryHeaderQueue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallInverseParameters

/-! Generate the normalization loader's eight binary parameters from retained
ordinary headers, rather than assuming its serialized queue. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def generateInverseParameters (source : Fin 8 → Fin T) (width word saved tmp dst carry : Fin T) : Pr P T Q A U :=
  binaryHeaderQueue width word saved tmp dst carry (List.ofFn source)

theorem generateInverseParameters_exec (source : Fin 8 → Fin T) (width word saved tmp dst carry : Fin T)
    (hregs : ∀ i, [source i,width,word,saved,tmp,dst].Nodup)
    (p u l target s t a b B : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = ![p,u,l,target,s,t,a,b] i)
    (hwidth : (S.R width).length = B) (hblank : ∀ i ∈ [word,saved,tmp], S.R i = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (p+u+l+target+s+t+a+b)*(4*B+10)+8*(8*B+12)+1 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+8*(2*(4*B+4))) depth
        (generateInverseParameters source width word saved tmp dst carry) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          ((inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms (A := A) B r.2)++S.R dst))}) := by
  have hwords : (List.ofFn source).flatMap (fun i => binSyms (A := A) (S.R width).length (S.R i).length) =
      (inverseParameterWords p u l target s t a b).flatMap (fun r => binSyms (A := A) B r.2) := by
    rw [List.flatMap_def,List.map_ofFn]
    simp only [Function.comp_def,hvalues,hwidth]
    rfl
  obtain ⟨v',n,hu,hn,he⟩ := binaryHeaderQueue_exec (body := body) width word saved tmp dst carry
    (List.ofFn source) (by
      intro src hsrc
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hsrc
      exact hregs i) v S hblank depth
  rw [hwidth,binaryHeaderQueueCost_eq] at hn
  have hsum : ((List.ofFn source).map (fun i => (S.R i).length)).sum = p+u+l+target+s+t+a+b := by
    rw [List.map_ofFn]
    simp only [Function.comp_def,hvalues]
    change p+(u+(l+(target+(s+(t+(a+(b+0))))))) = _
    omega
  rw [hsum,List.length_ofFn] at hn
  rw [hwords] at he
  exact ⟨v',n,hu,hn,by simpa only [generateInverseParameters,List.length_ofFn,hwidth] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
