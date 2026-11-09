module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadSupplierEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallRecoverySeedHeaders

/-! The ordinary origin reader writes directly into the changing recovery seed
ports. All other seed headers remain shared across jobs in a fitting class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

/-- Outside the two endpoint ports, seed headers depend only on shared numerical
parameters. In particular they do not depend on interval position or RHS data. -/
theorem recoverySeedHeader_eq_of_parameters (H K : ReplicaHaloProblem s)
    (hp : H.p = K.p) (hl : H.l = K.l) (ht : H.t = K.t) (hu : H.u = K.u)
    (htarget : H.target = K.target) (hrhs : H.rhsExp = K.rhsExp)
    (W N : ℕ) (i : Fin 392) (hi : i ∈ recoverySeedHeaderPorts)
    (ha : i ≠ 111) (hb : i ≠ 113) :
    recoverySeedHeader H W N i = recoverySeedHeader K W N i := by
  have hports : i = 97 ∨ i = 98 ∨ i = 99 ∨ i = 100 ∨ i = 101 ∨ i = 108 ∨
      i = 111 ∨ i = 112 ∨ i = 113 ∨ i = 114 ∨ i = 129 ∨ i = 130 ∨ i = 390 := by
    simpa [recoverySeedHeaderPorts,complexRecoveryHeaderPorts,derivedRecoveryHeaderPorts] using hi
  rcases hports with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader,generatedRecoveryHeader,
      replicaFactoryHeaderValue,ReplicaHaloProblem.precision,
      ReplicaHaloProblem.stage,ReplicaHaloProblem.band]

def readRecoverySeedEndpoints (width halo queue binary : Fin T) (source : Fin 392 → Fin T)
    (work saved tmp : Fin T) : Pr P T Q A U :=
  readSupplierEndpoints width halo queue binary (source 111) (source 113) work saved tmp

/-- Endpoint generation supplies the complete ordinary seed-header contract.
No unary origin or endpoint word is supplied by the caller. -/
theorem readRecoverySeedEndpoints_exec (H K : ReplicaHaloProblem s)
    (hp : H.p = K.p) (hl : H.l = K.l) (ht : H.t = K.t) (hu : H.u = K.u)
    (htarget : H.target = K.target) (hrhs : H.rhsExp = K.rhsExp) (W N V : ℕ)
    (width halo queue binary : Fin T) (source : Fin 392 → Fin T) (work saved tmp : Fin T)
    (hreg : [width,halo,queue,binary,source 111,source 113,work,saved,tmp].Nodup)
    (hoff : ∀ i ∈ recoverySeedHeaderPorts, i ≠ 111 → i ≠ 113 →
      source i ≠ queue ∧ source i ≠ source 111 ∧ source i ≠ source 113)
    (hfit : H.origin < 2^V) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = H.span)
    (hqueue : S.R queue = binSyms V H.origin++tail)
    (hblank : ∀ k ∈ [binary,source 111,source 113,work,saved,tmp], S.R k = [])
    (hvalues : ∀ i ∈ recoverySeedHeaderPorts, i ≠ 111 → i ≠ 113 →
      (S.R (source i)).length = recoverySeedHeader K W N i) (depth : ℕ) :
    let E := {S with R := Function.update (Function.update (Function.update S.R queue tail)
      (source 111) (List.replicate H.origin tick)) (source 113) (List.replicate (H.origin+H.span) tick)}
    ∃ v' n, v'.user = v.user ∧ n ≤ readSupplierEndpointsCost V H.origin H.span ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*readSupplierEndpointsCost V H.origin H.span) depth
        (readRecoverySeedEndpoints width halo queue binary source work saved tmp)
        (Host.mk v S) n (Host.mk v' E) ∧
      (∀ i ∈ recoverySeedHeaderPorts, (E.R (source i)).length = recoverySeedHeader H W N i) := by
  dsimp only
  obtain ⟨v',n,huser,hn,he⟩ := readSupplierEndpoints_exec_within (body := body)
    width halo queue binary (source 111) (source 113) work saved tmp hreg V H.origin H.span hfit
    tail v S hwidth hhalo hqueue hblank depth
  refine ⟨v',n,huser,hn,he,?_⟩
  have hr := hreg
  regs_ne hr
  intro i hi
  by_cases ha : i = 111
  · subst i
    simp only [Function.update_of_ne (show source 111 ≠ source 113 from by assumption),
      Function.update_self,List.length_replicate]
    simp [recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader,generatedRecoveryHeader]
  · by_cases hb : i = 113
    · subst i
      simp only [Function.update_self,List.length_replicate]
      simp [recoverySeedHeader,derivedRecoveryHeaderPorts,complexRecoveryHeader,generatedRecoveryHeader]
    · obtain ⟨hq,ha',hb'⟩ := hoff i hi ha hb
      simpa only [Function.update_of_ne hb',Function.update_of_ne ha',Function.update_of_ne hq] using
        (hvalues i hi ha hb).trans
          (recoverySeedHeader_eq_of_parameters H K hp hl ht hu htarget hrhs W N i hi ha hb).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
