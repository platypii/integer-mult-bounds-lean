module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratedChunkTile

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

theorem generatedChunkInterchangeCost_le (T t₀ P B d stock : ℕ) :
    generatedChunkInterchangeCost T t₀ P B d stock ≤
      (T+12*swapT t₀+5)*swapCost P 1 B d d (interchangeHeaderBits P 1 B d d)+
      6*stock+29*(P+B+2*d+1)+2*T+6*swapT t₀+122 := by
  have hh := interchangeHeaderVolume_le P 1 B d d
  dsimp only [generatedChunkInterchangeCost]
  omega

private theorem chunk_fields_le_volume {P B d V : ℕ} (hP : 0 < P) (hB : 0 < B)
    (hV : P*(2^d)*(2^d)*B = V) : P ≤ V ∧ B ≤ V ∧ d ≤ V := by
  have hK : 0 < 2^d := pow_pos (by decide) _
  have h₁ := Nat.le_mul_of_pos_right P hK
  have h₂ := Nat.le_mul_of_pos_right (P*2^d) hK
  have h₃ : P*2^d*2^d ≤ V := by rw [←hV]; exact Nat.le_mul_of_pos_right _ hB
  have h₄ : B ≤ V := by
    rw [←hV]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hP hK) hK)
  have h₅ := Nat.le_mul_of_pos_left (2^d) hP
  exact ⟨h₁.trans (h₂.trans h₃),h₄,(Nat.lt_two_pow_self (n := d)).le.trans (h₅.trans (h₂.trans h₃))⟩

/-- Every linear part of one actual stage is paid by its full tile volume and
initial placed-bank stock. Generated dimension masters are outside that bank. -/
theorem generatedChunkInterchangeCost_volume_le (T t₀ P B d stock V : ℕ)
    (hP : 0 < P) (hB : 0 < B) (hV : P*(2^d)*(2^d)*B = V) :
    generatedChunkInterchangeCost T t₀ P B d stock ≤
      (T+12*swapT t₀+5)*swapCost P 1 B d d (interchangeHeaderBits P 1 B d d)+
      200*(V+stock+T+swapT t₀+1) := by
  obtain ⟨hPV,hBV,hdV⟩ := chunk_fields_le_volume hP hB hV
  have hh := generatedChunkInterchangeCost_le T t₀ P B d stock
  nlinarith only [hh,hPV,hBV,hdV]

/-- The uniform supplier applies to all equal-chunk stages, with arbitrary
prefix and suffix dimensions. -/
theorem chunkSwapCost_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (P B d : ℕ), 0 < P → 0 < B →
      (swapCost P 1 B d d (interchangeHeaderBits P 1 B d d) : ℝ) ≤
        C*(P*(2^d)*(2^d)*B)*((max 1 d : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := swapCost_le
  refine ⟨C,hC,?_⟩
  intro P B d hP hB
  have hh := hbound P 1 B d d (interchangeHeaderBits P 1 B d d) hP (by decide) hB (by omega) (by omega)
    (by intro i; exact Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self _))
    (by intro i; exact binBits_size_canonical _)
  simp only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one,max_self] at hh
  push_cast at hh ⊢
  exact hh

private theorem dimensionBankLifecycleCost_le {K W c p b : ℕ}
    (hK : 1 ≤ K) (hW : 0 < W) (hp : p ≤ c) (hb : b ≤ c) :
    (unaryPowerChainCost K 1 p+unaryPowerChainCost K W b)+
      ((2*unaryPowerChainVolume K W b+2*b+1)+(2*unaryPowerChainVolume K 1 p+2*p+1)) ≤
        100*(c+1)*(K^c*K*W+1) := by
  let V := K^c*K*W
  have hKpos : 0 < K := by omega
  have hbig : K^c*W ≤ V := by
    calc
      _ ≤ (K^c*W)*K := Nat.le_mul_of_pos_right _ hKpos
      _ = V := by dsimp [V]; ring
  have hlastp : 1*K^p ≤ V := by
    calc
      _ ≤ K^c := by simpa only [Nat.one_mul] using Nat.pow_le_pow_right hK hp
      _ ≤ K^c*W := Nat.le_mul_of_pos_right _ hW
      _ ≤ V := hbig
  have hlastb : W*K^b ≤ V := by
    calc
      _ ≤ W*K^c := Nat.mul_le_mul_left W (Nat.pow_le_pow_right hK hb)
      _ = K^c*W := Nat.mul_comm _ _
      _ ≤ V := hbig
  have hKV : K ≤ V :=
    (Nat.le_mul_of_pos_left K (pow_pos hKpos c)).trans (Nat.le_mul_of_pos_right _ hW)
  have hvp := (unaryPowerChainVolume_le hK 1 p).trans (Nat.mul_le_mul hp hlastp)
  have hvb := (unaryPowerChainVolume_le hK W b).trans (Nat.mul_le_mul hb hlastb)
  have hkp := Nat.mul_le_mul hKV hp
  have hkb := Nat.mul_le_mul hKV hb
  rw [unaryPowerChainCost_eq,unaryPowerChainCost_eq]
  change _ ≤ 100*(c+1)*(V+1)
  nlinarith only [hvp,hvb,hkp,hkb,hp,hb]

/-- All non-interchange work in the actual enclosing tile is linear in tile
volume, initial bank stock and fixed register overhead, per address chunk. -/
theorem generatedChunkTileCost_linear_le {T t₀ d W stock c : ℕ}
    (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)) (hW : 0 < W)
    (hp : ps.length ≤ c) (hb : bs.length ≤ c)
    (hshape : (rs.map fun r => (r.outerCount,r.blockWidth)) = replicaChunkSwaps (2^d) W c) :
    generatedChunkTileCost T t₀ d W stock ps bs rs ≤
      (T+12*swapT t₀+5)*(rs.map (fun r => swapCost r.outerCount 1 r.blockWidth d d
        (interchangeHeaderBits r.outerCount 1 r.blockWidth d d))).sum+
      1000*(c+1)*((2^d)^c*(2^d)*W+stock+T+swapT t₀+1) := by
  let V := (2^d)^c*(2^d)*W
  let F := V+stock+T+swapT t₀+1
  let A := T+12*swapT t₀+5
  let bill := fun r : ChunkInterchangeStage T => swapCost r.outerCount 1 r.blockWidth d d
    (interchangeHeaderBits r.outerCount 1 r.blockWidth d d)
  have hready := chunkStages_shape_ready d W c hW rs hshape
  have hlen : rs.length = c := by
    have hh := congrArg List.length hshape
    simpa only [List.length_map,replicaChunkSwaps_length] using hh
  have hsum : (rs.map (fun r => generatedChunkInterchangeCost T t₀ r.outerCount r.blockWidth d stock)).sum ≤
      A*(rs.map bill).sum+200*rs.length*F := by
    have hs := List.sum_le_sum (l := rs) (fun r hr =>
      generatedChunkInterchangeCost_volume_le T t₀ r.outerCount r.blockWidth d stock V
        (hready r hr).1.1 (hready r hr).1.2 (by
          simpa only [BinaryAdjacentWidthInterchange.volume,Nat.mul_one] using (hready r hr).2.symm))
    refine hs.trans_eq ?_
    clear hs hlen hready hshape
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons] at ih ⊢
      rw [ih]
      dsimp only [A,F,bill]
      ring
  rw [hlen] at hsum
  have hbanks := dimensionBankLifecycleCost_le (Nat.one_le_pow d 2 (by decide)) hW hp hb
  unfold generatedChunkTileCost
  change _ ≤ A*(rs.map bill).sum+1000*(c+1)*F
  change _ ≤ A*(rs.map bill).sum+200*c*F at hsum
  change _ ≤ 100*(c+1)*(V+1) at hbanks
  have hVF : V+1 ≤ F := by dsimp [F]; omega
  have hmul := Nat.mul_le_mul_left (100*(c+1)) hVF
  have hpos : 1 ≤ F := by dsimp [F]; omega
  have hcf : 0 ≤ c*F := Nat.zero_le _
  nlinarith only [hsum,hbanks,hmul,hpos,hcf]

/-- A fixed number of equal-chunk swaps has the uniform supplier bound on the
original tile volume, even though prefix and suffix dimensions change. -/
theorem chunkSwapScheduleCost_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (d W c : ℕ), 0 < W →
      (((replicaChunkSwaps (2^d) W c).map (fun r =>
        swapCost r.1 1 r.2 d d (interchangeHeaderBits r.1 1 r.2 d d))).sum : ℝ) ≤
        C*c*((2^d)^c*(2^d)*W)*((max 1 d : ℕ) : ℝ)^Parameters.tau := by
  obtain ⟨C,hC,hbound⟩ := chunkSwapCost_uniform
  refine ⟨C,hC,?_⟩
  intro d W c
  induction c generalizing W with
  | zero => simp [replicaChunkSwaps]
  | succ c ih =>
    intro hW
    have hK : 0 < 2^d := pow_pos (by decide) _
    have hh := hbound ((2^d)^c) W d (pow_pos hK _) hW
    have ht := ih ((2^d)*W) (Nat.mul_pos hK hW)
    simp only [replicaChunkSwaps,List.map_cons,List.sum_cons]
    push_cast at hh ht ⊢
    rw [pow_succ]
    nlinarith only [hh,ht]

/-- The complete executed tile, including both generated dimension banks and
all header/cleanup work, has a uniform bound with one factor per chunk. -/
theorem generatedChunkTileCost_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ d W stock c : ℕ)
      (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)),
      0 < W → ps.length ≤ c → bs.length ≤ c →
      (rs.map (fun r => (r.outerCount,r.blockWidth))) = replicaChunkSwaps (2^d) W c →
      (generatedChunkTileCost T t₀ d W stock ps bs rs : ℝ) ≤
        C*(T+12*swapT t₀+5)*c*((2^d)^c*(2^d)*W)*((max 1 d : ℕ) : ℝ)^Parameters.tau+
        1000*(c+1)*((2^d)^c*(2^d)*W+stock+T+swapT t₀+1) := by
  obtain ⟨C,hC,hbound⟩ := chunkSwapScheduleCost_uniform
  refine ⟨C,hC,?_⟩
  intro T t₀ d W stock c ps bs rs hW hp hb hshape
  have hs := hbound d W c hW
  have hl : (generatedChunkTileCost T t₀ d W stock ps bs rs : ℝ) ≤
      (((T+12*swapT t₀+5)*(rs.map (fun r => swapCost r.outerCount 1 r.blockWidth d d
        (interchangeHeaderBits r.outerCount 1 r.blockWidth d d))).sum+
        1000*(c+1)*((2^d)^c*(2^d)*W+stock+T+swapT t₀+1) : ℕ) : ℝ) := by
    exact_mod_cast generatedChunkTileCost_linear_le ps bs rs hW hp hb hshape
  have he : (rs.map (fun r => swapCost r.outerCount 1 r.blockWidth d d
      (interchangeHeaderBits r.outerCount 1 r.blockWidth d d))).sum =
      ((replicaChunkSwaps (2^d) W c).map (fun r => swapCost r.1 1 r.2 d d
        (interchangeHeaderBits r.1 1 r.2 d d))).sum := by
    rw [←hshape,List.map_map]
    rfl
  rw [he] at hl
  have hm := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ T+12*swapT t₀+5 by positivity)
  push_cast at hl hm ⊢
  nlinarith only [hl,hm]

/-- Encoding, both actual tile routes, old-payload disposal and reassembly keep
the same uniform routing exponent; all additional codec passes are linear. -/
theorem packedGeneratedChunkTileCost_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t₀ d W stock c : ℕ)
      (ps bs : List (Fin T)) (rs : List (ChunkInterchangeStage T)),
      0 < W → ps.length ≤ c → bs.length ≤ c →
      (rs.map (fun r => (r.outerCount,r.blockWidth))) = replicaChunkSwaps (2^d) W c →
      (packedGeneratedChunkTileCost T t₀ d W c stock ps bs rs : ℝ) ≤
        C*(T+12*swapT t₀+5)*c*((2^d)^c*(2^d)*W)*((max 1 d : ℕ) : ℝ)^Parameters.tau+
        2000*(c+1)*(3*((2^d)^c*(2^d)*W)+stock+T+swapT t₀+1)+22*((2^d)^c*(2^d)*W)+20 := by
  obtain ⟨C,hC,hbound⟩ := generatedChunkTileCost_uniform
  refine ⟨2*C,by positivity,?_⟩
  intro T t₀ d W stock c ps bs rs hW hp hb hshape
  have hh := hbound T t₀ d W (stock+2*((2^d)^c*(2^d)*W)) c ps bs rs hW hp hb hshape
  dsimp only [packedGeneratedChunkTileCost]
  simp only [Nat.mul_assoc] at hh ⊢
  push_cast at hh ⊢
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
