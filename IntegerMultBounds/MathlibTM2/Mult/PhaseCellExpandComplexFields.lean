module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExpandComplexKeyCounted
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchInputData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComponentInputs

/-! Component expansion supplies the actual packed solver's ordered field ABI. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def complexComponentFields {s : ℕ} (Fs : List (ZMod s → GaussianInt)) :
    List (ZMod s → GaussianInt) :=
  Fs.map (fun F i => realPartWord (F i))++Fs.map (fun F i => imagPartWord (F i))

@[simp] theorem complexComponentFields_length {s : ℕ} (Fs : List (ZMod s → GaussianInt)) :
    (complexComponentFields Fs).length = 2*Fs.length := by
  simp [complexComponentFields,two_mul]

theorem complexComponentFields_norm_le {s : ℕ} (p : ℕ) (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∀ F ∈ complexComponentFields Fs, ∀ i, ‖value p (F i)‖ ≤ 1 := by
  intro F hmem i
  rcases List.mem_append.mp hmem with hmem | hmem
  · obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hmem
    exact (componentWords_norm_le p (G i)).1.trans (hF G hG i)
  · obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hmem
    exact (componentWords_norm_le p (G i)).2.trans (hF G hG i)

/-- Splitting a flat key is the same ordered input as mapping each field first.
Both components retain the original ambient coordinates and local interval. -/
theorem packedBatch_components {s : ℕ} (a L : ℕ) (Fs : List (ZMod s → GaussianInt)) :
    ((Fs.map (packedInterval a L)).flatten).map realPartWord++
      ((Fs.map (packedInterval a L)).flatten).map imagPartWord =
        ((complexComponentFields Fs).map (packedInterval a L)).flatten := by
  simp only [packedBatch_map,complexComponentFields,List.map_append,List.flatten_append,
    List.map_map,Function.comp_def]

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Start with N local complex packets and establish exactly the 2N real input
packets expected by the numerical batch, retaining N for output pairing. -/
theorem expandComplexFields_exec {replicas width count src imag saved tmp hold : Fin T}
    (hreg : [replicas,width,count,src,imag,saved,tmp,hold].Nodup) (hA : 4 ≤ A)
    {s : ℕ} (a L W : ℕ) (hfit : a+L ≤ s) (Fs : List (ZMod s → GaussianInt))
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = Fs.length) (hwidth : (S.R width).length = L*W)
    (hsrc : S.R src = cstream A W ((Fs.map (packedInterval a L)).flatten)++tail)
    (hcount : S.R count = []) (himag : S.R imag = []) (hsaved : S.R saved = [])
    (htmp : S.R tmp = []) (hhold : S.R hold = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ Fs.length*(26*(L*W)+17)+34 ∧
      Exec body (expandComplexKeyCounted replicas width count src imag saved tmp hold) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R hold
          (List.replicate Fs.length tick)) src
            (cstream A W (((complexComponentFields Fs).map (packedInterval a L)).flatten)++tail))
              replicas (List.replicate Fs.length tick++S.R replicas))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := expandComplexKeyCounted_exec (body := body) hreg hA Fs.length (L*W) W
    ((Fs.map (packedInterval a L)).flatten)
    (by rw [packedBatch_length a L Fs hfit]; ring) tail v S
    hreplicas hwidth hsrc hcount himag hsaved htmp hhold
  exact ⟨v',n,hu,hn,by simpa only [packedBatch_components] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
