module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizePackedRecoveryPiece
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock

/-! Injective placement of packed normalization changes only its borrowed source.
The local executor has no calls, so it embeds in any caller body. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedRecoveryNormalization
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def placedNormalizePiece (e : Fin 64 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (normalizePiece (P := Empty))

theorem placedNormalizePiece_exec (eReg : Fin 64 → Fin T) (hReg : Function.Injective eReg) (hA : 4 ≤ A)
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
    (v : HS T Q A U) (S : Stacks T A)
    (hP : (S.R (eReg 0)).length = 2^15*p) (hq : (S.R (eReg 1)).length = q)
    (ha : (S.R (eReg 2)).length = a) (hb : (S.R (eReg 3)).length = a+L)
    (hvolume : (S.R (eReg 4)).length = L*(2*q+8)) (hreplicas : (S.R (eReg 5)).length = Ds.length)
    (hwide : (S.R (eReg 6)).length = W)
    (hsrc : S.R (eReg 7) = (Ds.map (fun D => cstream A (2*q+8) (packedInterval a L D))).flatten++tail)
    (hfresh : ∀ i : Fin 64, 8 ≤ i.val → S.R (eReg i) = []) :
    let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
    ∃ v' n, v'.user = v.user ∧ n ≤ normalizationCost p q W a L Ds.length ∧
      Exec body (placedNormalizePiece eReg) (mk v S) n (mk v' {S with R := (Function.update S.R (eReg 7)
        ((Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn active
        (packedIntervalRead p W a (cstream A W (packedInterval a L D)++tail))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (2/(2 : ℝ)^p+e/(2 : ℝ)^inverseNormalizationShift p)) xs Gs := by
  dsimp only
  let Gs := Ds.map (fun D i => finalRoundWord (2*q+8) q p (inverseNormalizationShift p) (D i))
  let ys := (Gs.map (fun D => cstream A W (packedInterval a L D))).flatten++tail
  obtain ⟨vi,n,hu,hn,hex,haccuracy⟩ := normalizePiece_exec (body := fun z : Empty => nomatch z)
    hA p q W a L hpq hsize hW hinterval active hactive hcover xs Ds e he hx hreal hfits tail hgood
    (embDn eReg v) (embStk eReg S) hP hq ha hb hvolume hreplicas hwide hsrc hfresh
  obtain ⟨v',hv,hu',hex'⟩ := exec_emb_ovr (body' := body) (e := eReg) (ι := Empty.elim)
    hReg (fun z => nomatch z) hex v rfl S rfl
  have hstate : embOvr eReg {embStk eReg S with R := Function.update (embStk eReg S).R 7 ys}.get S =
      {S with R := Function.update S.R (eReg 7) ys} := by
    rw [embOvr_updR hReg,embOvr_stk]
  exact ⟨v',n,hu'.trans hu,hn,hex'.cast rfl (congrArg (mk v') hstate),haccuracy⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.PackedRecoveryNormalization
