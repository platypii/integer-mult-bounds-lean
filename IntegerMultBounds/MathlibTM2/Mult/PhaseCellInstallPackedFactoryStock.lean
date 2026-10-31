module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallPackedFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactoryGeometryStock

/-! The generated packed factory bank carries a linear setup-stock trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

open IntegerMultBounds.MathlibTM2.Fast.Main
theorem installPackedFactory_exec_within (work : Fin 242 → Fin T) (hwork : Function.Injective work)
    (source : Fin 10 → Fin T) (width span tmp saved carry : Fin T)
    (hsourceOff : ∀ i j, source i ≠ work j) (hsourceTmp : ∀ i, source i ≠ tmp)
    (hworkTmp : ∀ i, work i ≠ tmp)
    (hgeometry : [source 8,source 9,width,work 155,work 165,work 163,span,tmp,saved].Nodup)
    (P N q l s t u band a b V : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvalues : ∀ i, (S.R (source i)).length = masterHeaderValues P N q l s t u band a b i)
    (hwidth : (S.R width).length = V) (hwidthOff : ∀ i, width ≠ work i)
    (hblank : ∀ i, S.R (work i) = []) (hleft : ∀ i, S.L (work i) = [])
    (hscratch : ∀ i ∈ [span,tmp,saved], S.R i = [])
    (hscratchOff : ∀ i ∈ [span,tmp,saved], ∀ j, i ≠ work j) (depth : ℕ) :
    let rs := masterHeaderCopies (work ∘ packedFactoryNativeReg) source
    let value := fun i => (S.R i).length
    let M := {S with R := unaryCopiesR value S.R rs}
    let F := {M with R := (Function.update (Function.update (Function.update M.R (work 163)
      (List.replicate V tick)) (work 155) (binSyms V a)) (work 165) (binSyms V (b-a)))}
    ∃ v' n, v'.user = v.user ∧ n ≤ copyUnaryHeadersCost value rs + factoryGeometryCost a b V ∧
      embStk work F = packedFactoryInputBank (embStk work S) P N q l s t u band a b V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*copyUnaryHeadersCost value rs+(8*a+8*b+24*V+40))) depth (installPackedFactory work source width span tmp saved carry) (mk v S) n (mk v' F) := by
  dsimp only
  let rs := masterHeaderCopies (work ∘ packedFactoryNativeReg) source
  let value := fun i => (S.R i).length
  let M : Stacks T A := {S with R := unaryCopiesR value S.R rs}
  obtain ⟨v₁,hu₁,hbank,_,he₁⟩ := installMasterHeaderBank_exec (body := body)
    (work ∘ packedFactoryNativeReg) (hwork.comp packedFactoryNativeReg_injective) source tmp
    (fun i j => hsourceOff i _) hsourceTmp (fun i => hworkTmp _) P N q l s t u band a b v S
    hvalues (fun i => hblank _) (fun i => hleft _) (hscratch tmp (by simp)) depth
  have hoff (i : Fin T) (hi : ∀ j, i ≠ work (packedFactoryNativeReg j)) : M.R i = S.R i := by
    apply unaryCopiesR_off
    intro r hr he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hi _ he.symm
  have hsource (i : Fin 10) : M.R (source i) = S.R (source i) := hoff _ (fun j => hsourceOff i _)
  have hgap (k : Fin 242) (hk : 154 ≤ k.val) (hk' : k.val < 168) : M.R (work k) = [] := by
    rw [hoff _ (fun j he => (packedFactoryNativeReg_gap j k hk hk') (hwork he).symm),hblank]
  have hblankGeometry : ∀ i ∈ [work 155,work 165,work 163,span,tmp,saved], M.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hgap _ (by decide) (by decide)
    · exact hgap _ (by decide) (by decide)
    · exact hgap _ (by decide) (by decide)
    all_goals rw [hoff _ (fun j => hscratchOff _ (by simp) _),hscratch _ (by simp)]
  obtain ⟨v₂,n,hu₂,hn,he₂⟩ := factoryGeometry_exec_within (body := body)
    (source 8) (source 9) width (work 155) (work 165) (work 163) span tmp saved carry hgeometry
    a b V v₁ M
    (by rw [hsource]; exact hvalues 8) (by rw [hsource]; exact hvalues 9)
    (by rw [hoff _ (fun j => hwidthOff _)]; exact hwidth) hblankGeometry depth
  have hwhole := mn_seq_within_add he₁ he₂
  obtain ⟨vf,nf,hu,hcost,hbank,hex⟩ := installPackedFactory_exec (body := body)
    work hwork source width span tmp saved carry hsourceOff hsourceTmp hworkTmp hgeometry
    P N q l s t u band a b V v S hvalues hwidth hwidthOff hblank hleft hscratch hscratchOff
  obtain ⟨hsteps,hfinal⟩ := hwhole.toExec.unique hex
  rw [hsteps,hfinal] at hwhole
  exact ⟨vf,nf,hu,hcost,hbank,hwhole⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
