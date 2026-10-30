module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerWorkspace

/-! Generated master headers establish retained-solver readiness on an otherwise clean native bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The ten ordinary master words, independent of how precision was selected. -/
def masterHeaderValues (P N q l s t u band a b : ℕ) : Fin 10 → ℕ :=
  ![P,N,q,l,s,t,u,band,a,b]

/-- Clean storage plus the ten master words establishes native loop readiness. -/
theorem masterHeaders_ready {A P N q l s t u band a b : ℕ}
    (S : Stacks 224 A) (input : List (Fin (A+4)))
    (hleft : ∀ k, S.L k = [])
    (hheaders : ∀ i, S.R (inverseMasterCorePort i) =
      List.replicate (masterHeaderValues P N q l s t u band a b i) Node.tick)
    (hblank : ∀ k, (∀ i, inverseMasterCorePort i ≠ k) → k ≠ 110 → k ≠ 132 → S.R k = [])
    (hsource : S.R 110 = input) :
    LengthKeyReady P N q l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) := by
  have hlen (i : Fin 10) : (S.R (inverseMasterCorePort i)).length = masterHeaderValues P N q l s t u band a b i := by
    rw [hheaders,List.length_replicate]
  have hb (k : Fin 224) (hports : ∀ i, inverseMasterCorePort i ≠ k) (h110 : k ≠ 110) (h132 : k ≠ 132) :
      S.R k = [] := hblank k hports h110 h132
  have h128 : S.R 128 = [] := hb 128 (by intro i; fin_cases i <;> decide) (by decide) (by decide)
  constructor
  · intro r hr
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 0
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 1
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 2
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 3
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 4
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 5
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 6
      | simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,
          inverseMasterCorePort,masterHeaderValues] using hlen 7
      | simp [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue,h128]
  · intro k hk
    exact hleft _
  · intro k hk hk93 hk110
    change S.R (boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg k)))) = []
    apply hb
    · intro i
      fin_cases i <;> dsimp [inverseMasterCorePort,boundaryFactorLegacyReg,tableReg,boundaryArithmeticReg,componentReg]
      all_goals split_ifs <;> simp_all only [Fin.ext_iff] <;> omega
    · dsimp [boundaryFactorLegacyReg,tableReg,boundaryArithmeticReg,componentReg]
      split_ifs <;> simp_all only [Fin.ext_iff] <;> omega
    · dsimp [boundaryFactorLegacyReg,tableReg,boundaryArithmeticReg,componentReg]
      split_ifs <;> simp_all only [Fin.ext_iff] <;> omega
  · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using hsource
  · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using
      hb 129 (by intro i; fin_cases i <;> decide) (by decide) (by decide)
  · simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using
      hb 133 (by intro i; fin_cases i <;> decide) (by decide) (by decide)
  · have hh := hb 130 (by intro i; fin_cases i <;> decide) (by decide) (by decide)
    simp [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,hh]
  · have hh := hb 125 (by intro i; fin_cases i <;> decide) (by decide) (by decide)
    simp [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,hh]
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg] using
        hb _ (by intro i; fin_cases i <;> decide) (by decide) (by decide)


theorem inverseHeaders_ready {A p u l target s t a b : ℕ} [NeZero s]
    (S : Stacks 224 A) (input : List (Fin (A+4)))
    (hleft : ∀ k, S.L k = [])
    (hheaders : ∀ i, S.R (inverseMasterCorePort i) = List.replicate (inverseMasterValues p u l target s t a b i) Node.tick)
    (hblank : ∀ k, (∀ i, inverseMasterCorePort i ≠ k) → k ≠ 110 → k ≠ 132 → S.R k = [])
    (hsource : S.R 110 = input) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let E := inverseExecutionExponent p l target N band
    LengthKeyReady (2^15*p) (2*E+1) (4*E) l s t u band 0 0 input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))) := by
  dsimp only
  exact masterHeaders_ready S input hleft hheaders hblank hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
