module

public import IntegerMultBounds.MathlibTM2.Host.SharedRegisterPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPublicationOrigins

/-! The origin scan reuses the fresh routing suffix. Only four retained binary
geometry words, their width and the two generated outputs use caller ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open PackedTranspose
noncomputable section
variable {T A : ℕ}

/-- Borrow the numerical geometry and use the owned publication packet ports. -/
def publicationRetainedOriginSources (routeSrc : Fin 7 → Fin T) (pubSrc : Fin 10 → Fin T) : Fin 7 → Fin T :=
  ![routeSrc 0,routeSrc 1,routeSrc 2,routeSrc 3,routeSrc 4,pubSrc 9,pubSrc 6]

theorem publicationRetainedOriginSources_route (routeSrc : Fin 7 → Fin T) (pubSrc : Fin 10 → Fin T) (j : Fin 5) :
    publicationRetainedOriginSources routeSrc pubSrc (Fin.castAdd 2 j) = routeSrc (Fin.castAdd 2 j) := by
  fin_cases j <;> rfl

theorem publicationRetainedOriginSources_packet (routeSrc : Fin 7 → Fin T) (pubSrc : Fin 10 → Fin T) :
    publicationRetainedOriginSources routeSrc pubSrc 5 = pubSrc 9 := rfl

theorem publicationRetainedOriginSources_count (routeSrc : Fin 7 → Fin T) (pubSrc : Fin 10 → Fin T) :
    publicationRetainedOriginSources routeSrc pubSrc 6 = pubSrc 6 := rfl

def publicationOriginIndex (j : Fin 7) : Fin 117 := ![32,33,34,35,37,109,116] j

def publicationOriginRole (i : Fin 117) : Option (Fin 7) :=
  if i = 32 then some 0 else if i = 33 then some 1 else if i = 34 then some 2 else
  if i = 35 then some 3 else if i = 37 then some 4 else if i = 109 then some 5 else
  if i = 116 then some 6 else none

theorem publicationOriginRole_index (j : Fin 7) : publicationOriginRole (publicationOriginIndex j) = some j := by
  fin_cases j <;> decide +kernel

theorem publicationOriginRole_recovers (i : Fin 117) (j : Fin 7)
    (hi : publicationOriginRole i = some j) : i = publicationOriginIndex j := by
  unfold publicationOriginRole at hi
  split_ifs at hi <;> simp_all only [Option.some.injEq,reduceCtorEq] <;> subst_vars <;> rfl

def publicationOriginPlacement (src : Fin 7 → Fin T) : Fin 117 → Fin (T+tapeCount) :=
  sharedRegisterPlacement (fun i => Fin.natAdd T (publicationReg i))
    (Fin.castAdd tapeCount ∘ src) publicationOriginRole

theorem publicationOriginPlacement_shared (src : Fin 7 → Fin T) (j : Fin 7) :
    publicationOriginPlacement src (publicationOriginIndex j) = Fin.castAdd tapeCount (src j) := by
  simp only [publicationOriginPlacement,sharedRegisterPlacement,publicationOriginRole_index,Function.comp_apply]

theorem publicationOriginPlacement_private (src : Fin 7 → Fin T) (i : Fin 117)
    (hi : publicationOriginRole i = none) :
    publicationOriginPlacement src i = Fin.natAdd T (publicationReg i) := by
  simp only [publicationOriginPlacement,sharedRegisterPlacement,hi]

theorem publicationOriginPlacement_injective (src : Fin 7 → Fin T) (hinj : Function.Injective src) :
    Function.Injective (publicationOriginPlacement src) := by
  apply sharedRegisterPlacement_injective
  · exact (Fin.natAdd_injective _ _).comp publicationReg_injective
  · exact (Fin.castAdd_injective _ _).comp hinj
  · intro i j; exact (prefix_ne_routing _ _).symm
  · intro i k j hi hk
    exact (publicationOriginRole_recovers i j hi).trans (publicationOriginRole_recovers k j hk).symm

theorem publicationOriginPlacement_off_prefix (src : Fin 7 → Fin T) (k : Fin T)
    (hoff : ∀ j, src j ≠ k) (i : Fin 117) :
    publicationOriginPlacement src i ≠ Fin.castAdd tapeCount k := by
  unfold publicationOriginPlacement sharedRegisterPlacement
  cases hr : publicationOriginRole i with
  | none => exact (prefix_ne_routing _ _).symm
  | some j => exact (Fin.castAdd_injective _ _).ne (hoff j)

theorem publicationOriginPlacement_input (src : Fin 7 → Fin T)
    (S : Stacks (T+tapeCount) A) (V s width radius L : ℕ)
    (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwords : ∀ j : Fin 4, S.R (Fin.castAdd tapeCount (src (Fin.castAdd 3 j))) = binSyms V (![s,width,radius,L] j))
    (hV : (S.R (Fin.castAdd tapeCount (src 4))).length = V)
    (hblank : ∀ i, S.R (Fin.natAdd T i) = []) :
    PublicationOriginInput (publicationOriginPlacement src) V s width radius L S := by
  have hread := publicationOriginPlacement_shared src
  have hfresh (i : Fin 117) (hi : publicationOriginRole i = none) :
      S.R (publicationOriginPlacement src i) = [] := by
    rw [publicationOriginPlacement_private src i hi,hblank]
  refine ⟨hwide,hLfit,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [show (37 : Fin 117) = publicationOriginIndex 4 from rfl,hread]; exact hV
  · rw [show (32 : Fin 117) = publicationOriginIndex 0 from rfl,hread]; exact hwords 0
  · rw [show (33 : Fin 117) = publicationOriginIndex 1 from rfl,hread]; exact hwords 1
  · rw [show (34 : Fin 117) = publicationOriginIndex 2 from rfl,hread]; exact hwords 2
  · rw [show (35 : Fin 117) = publicationOriginIndex 3 from rfl,hread]; exact hwords 3
  · exact hfresh 36 (by decide +kernel)
  · intro i hi
    apply hfresh
    have hne (j : Fin 117) (hj : 31 ≤ j.val) : i ≠ j := by intro he; subst i; omega
    simp [publicationOriginRole,hne 32 (by decide),hne 33 (by decide),hne 34 (by decide),
      hne 35 (by decide),hne 37 (by decide),hne 109 (by decide),hne 116 (by decide)]
  · exact hfresh 104 (by decide +kernel)
  · exact hfresh 106 (by decide +kernel)

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
