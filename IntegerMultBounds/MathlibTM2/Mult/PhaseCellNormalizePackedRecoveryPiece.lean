module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryNormalizationLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedNormalizePackedRealBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationWidth

/-! Normalize one physical piece archive using only retained recovery masters.
The generated width/length rulers and scalar bank are fully retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedRecoveryNormalization
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 64 Q A U}

def normalizePiece : Pr P 64 Q A U :=
  .seq (generateCyclicNormalizationWidth 0 1 33 52 53 54 55 56)
    (.seq (ucopy 3 58 55)
      (.seq (usub 2 58 55)
        (.seq (retainedNormalizePackedRealBatch scalar ports 52 53 54 55 56 0 1 57 6 58 5 4 59 7 60 61 62 63)
          (clearWords [58,33]))))

def normalizationCost (p q W a L N : ℕ) : ℕ :=
  let B := cyclicNormalizationWidth (2^15*p) q
  (19*(2^15*p)+19*q+17)+(4*(a+L)+4)+(4*a+4)+
    ((1+(2^15*p+q)*(4*B+10)+2*(8*B+12))+25*(4*B+4)+2*(8*B+8)+2+
      (18+(4*Nat.size (4*p)+31))*tblC B 0+
      normalizePackedBatchCost B (2*q+8) p W N L+(8*p+11*B+9)+(2*(25*B)+2*25+1))+
    (2*(L+B)+5)

theorem normalizePiece_exec (hA : 4 ≤ A)
    (p q W a L : ℕ) (hpq : p ≤ q)
    (hsize : q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8) (hW : 2*p+13 ≤ W)
    {s : ℕ} [NeZero s] (hinterval : a+L ≤ s)
    (active : Finset (ZMod s)) (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (hcover : ∀ i : ZMod s, a ≤ i.val → i.val < a+L → i ∈ active)
    (xs : List (ZMod s → ℝ)) (Ds : List (ZMod s → GaussianInt)) (e : ℝ) (he : e ≤ 1)
    (hx : ∀ x ∈ xs, ∀ i ∈ active, ‖x i‖ ≤ 4*(2 : ℝ)^(p+8))
    (hreal : ∀ D ∈ Ds, ∀ i, (D i).im = 0) (hfits : ∀ D ∈ Ds, ∀ i, Fits (2*q+8) (D i))
    (tail : List (Fin (A+4)))
    (hgood : List.Forall₂ (fun x D =>
      PhaseCellInterface.ErrorOn active (fun i => (value q (D i)).re) x e) xs Ds)
    (v : HS 64 Q A U) (S : Stacks 64 A)
    (hP : (S.R 0).length = 2^15*p) (hq : (S.R 1).length = q)
    (ha : (S.R 2).length = a) (hb : (S.R 3).length = a+L)
    (hvolume : (S.R 4).length = L*(2*q+8)) (hreplicas : (S.R 5).length = Ds.length)
    (hwide : (S.R 6).length = W)
    (hsrc : S.R 7 = (Ds.map (fun D => cstream A (2*q+8) (packedInterval a L D))).flatten++tail)
    (hfresh : ∀ i : Fin 64, 8 ≤ i.val → S.R i = []) :
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
    ∃ v' n, v'.user = v.user ∧ n ≤ normalizationCost p q W a L Ds.length ∧
      Exec body normalizePiece (mk v S) n (mk v' {S with R := (Function.update S.R 7
        ((Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W a (cstream A W (packedInterval a L D)++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p)) xs Gs := by
  dsimp only
  let B := cyclicNormalizationWidth (2^15*p) q
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generateCyclicNormalizationWidth_exec (body := body)
    (kernel := 0) (precision := 1) (width := 33) (a := 52) (h := 53) (par := 54) (bits := 55) (saved := 56)
    (by decide) (2^15*p) q v S hP hq (hfresh 33 (by decide))
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by decide))
  let E : Stacks 64 A := {S with R := Function.update S.R 33 (List.replicate B tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := 3) (b := 58) (t := 55)
    (by decide) (by decide) (by decide) v₁ E (by simpa [E] using hfresh 55 (by decide))
  let F : Stacks 64 A := {E with R := Function.update E.R 58 (List.replicate (a+L) tick)}
  have he₂' : Exec body (ucopy 3 58 55) (mk v₁ E) (4*(a+L)+4) (mk v₂ F) := by
    simpa [F,E,hb,hfresh 58 (by decide)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec body (a := 2) (b := 58) (t := 55)
    (by decide) (by decide) (by decide) v₂ F (by simpa [F,E] using hfresh 55 (by decide))
  let G : Stacks 64 A := {E with R := Function.update E.R 58 (List.replicate L tick)}
  have he₃' : Exec body (usub 2 58 55) (mk v₂ F) (4*a+4) (mk v₃ G) := by
    simpa [G,F,E,ha] using he₃
  have hread (i : Fin 64) (h33 : i ≠ 33) (h58 : i ≠ 58) : G.R i = S.R i := by
    simp only [G,E,Function.update_of_ne h33,Function.update_of_ne h58]
  have hblank (i : Fin 64) (hi : 8 ≤ i.val) (h33 : i ≠ 33) (h58 : i ≠ 58) : G.R i = [] :=
    (hread i h33 h58).trans (hfresh i hi)
  have hbankBlank (r : TblR 25) (hr : r ≠ .wr) : G.R (scalar r) = [] := by
    have h33 : scalar r ≠ 33 := by
      have hw : scalar .wr = 33 := rfl
      rw [←hw]
      exact scalar_injective.ne hr
    exact hblank _ (scalar_range r).1 h33 (scalar_ne r 58 (by decide))
  have hroom := cyclicNormalizationWidth_room p q
  obtain ⟨vf,m,hu,hm,hexec,haccuracy⟩ := retainedNormalizePackedRealBatch_exec (body := body) hA scalar scalar_injective
    ports ports_injective 52 53 54 55 56 0 1 57 6 58 5 4 59 7 60 61 62 63
    (by intro r; exact scalar_ne r 52 (by decide))
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl <;> decide +kernel)
    (by decide +kernel)
    (by intro k hk r
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact scalar_ne r _ (by decide))
    (by intro i r; exact scalar_ne r (ports i) (Or.inr (by simp [ports])))
    B p q W (List.replicate B tick) (by simp) hroom.1 hroom.2.1 hroom.2.2 hpq hsize hW
    a L hinterval active hactive hcover xs Ds e he hx hreal hfits tail hgood v₃ G
    (by simp [G,E,scalar]) hbankBlank
    (by simpa only [hread 0 (by decide) (by decide)] using hP)
    (by simpa only [hread 1 (by decide) (by decide)] using hq)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact hblank _ (by decide) (by decide) (by decide))
    (hblank 57 (by decide) (by decide) (by decide))
    (by simpa only [hread 6 (by decide) (by decide)] using hwide)
    (by simp [G])
    (by simpa only [hread 5 (by decide) (by decide)] using hreplicas)
    (by simpa only [hread 4 (by decide) (by decide)] using hvolume)
    (by simpa only [hread 7 (by decide) (by decide)] using hsrc)
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact hblank _ (by decide) (by decide) (by decide))
    (by intro i
        apply hblank (ports i) (by change 8 ≤ 48+i.val; omega)
        · intro heq
          have hv := congrArg Fin.val heq
          change 48+i.val = 33 at hv
          omega
        · intro heq
          have hv := congrArg Fin.val heq
          change 48+i.val = 58 at hv
          omega)
  let ys := ((Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))).map
    (fun D => cstream A W (packedInterval a L D))).flatten++tail
  let G' : Stacks 64 A := {G with R := Function.update G.R 7 ys}
  obtain ⟨v',hu',he'⟩ := clearWords_exec (body := body) [58,33] (by decide) vf G'
  have hc : binaryHeaderQueueCost G.R B [0,1] =
      1+(2^15*p+q)*(4*B+10)+2*(8*B+12) := by
    simp [binaryHeaderQueueCost,G,E,hP,hq]
    ring
  have hfinal : {G' with R := fun i => if i ∈ ([58,33] : List (Fin 64)) then [] else G'.R i} =
      {S with R := Function.update S.R 7 ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h58 : i = 58
    · subst i; simp [hfresh 58 (by decide)]
    by_cases h33 : i = 33
    · subst i; simp [hfresh 33 (by decide)]
    simp [G',G,E,Function.update_apply,h58,h33]
  have he'' : Exec body (clearWords [58,33]) (mk vf G') (2*(L+B)+5)
      (mk v' {S with R := Function.update S.R 7 ys}) := by
    have hcost : 2*(([58,33].map (fun i => (G'.R i).length)).sum)+2*[58,33].length+1 = 2*(L+B)+5 := by
      simp [G',G,E,List.sum_cons,List.sum_nil]

    exact he'.cast hcost (congrArg (mk v') hfinal)
  refine ⟨v',m₁+((4*(a+L)+4)+((4*a+4)+(m+(2*(L+B)+5)))),
    hu'.trans (hu.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq hexec he''))),haccuracy⟩
  rw [hc] at hm
  dsimp only [B] at hm
  dsimp only [normalizationCost,B]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedRecoveryNormalization
