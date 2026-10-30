module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairComplexKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedPairAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchInputData

/-! Ordered local real/imaginary batch assembly, with the executed output's error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def pairedComponentFields {s : ℕ} (Xs Ys : List (ZMod s → GaussianInt)) :
    List (ZMod s → GaussianInt) := List.zipWith (fun X Y i => pairComponentWord (X i) (Y i)) Xs Ys

theorem packedInterval_pair {s : ℕ} (a L : ℕ) (X Y : ZMod s → GaussianInt) :
    List.zipWith pairComponentWord (packedInterval a L X) (packedInterval a L Y) =
      packedInterval a L (fun i => pairComponentWord (X i) (Y i)) := by
  simp [packedInterval,chirpLine,← List.map_take,← List.map_drop,List.zipWith_map,List.zipWith_self]

theorem packedBatch_pair {s : ℕ} (a L : ℕ) (hfit : a+L ≤ s)
    (Xs Ys : List (ZMod s → GaussianInt)) (hlen : Xs.length = Ys.length) :
    List.zipWith pairComponentWord (Xs.map (packedInterval a L)).flatten
      (Ys.map (packedInterval a L)).flatten =
        ((pairedComponentFields Xs Ys).map (packedInterval a L)).flatten := by
  induction Xs generalizing Ys with
  | nil => cases Ys <;> simp_all [pairedComponentFields]
  | cons X Xs ih =>
    cases Ys with
    | nil => simp at hlen
    | cons Y Ys =>
      simp only [List.length_cons,Nat.succ.injEq] at hlen
      simp only [List.map_cons,List.flatten_cons,pairedComponentFields,List.zipWith_cons_cons]
      rw [List.zipWith_append (by simp [packedInterval_length _ hfit]),packedInterval_pair,ih Ys hlen]
      rfl

/-- Component errors combine per replica; list length never multiplies error. -/
theorem pairedComponentFields_accuracy {A s : ℕ} [NeZero s] (hA : 4 ≤ A)
    (q w a L : ℕ) (active : Finset (ZMod s)) (hfit : a+L ≤ s)
    (hactive : ∀ i ∈ active, a ≤ i.val ∧ i.val < a+L)
    (Zs : List (ZMod s → ℂ)) (Xs Ys : List (ZMod s → GaussianInt))
    (eX eY : ℝ) (tailX tailY tail : List (Fin (A+4)))
    (hX : List.Forall₂ (fun z X => PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L X)++tailX) i).re)
      (fun i => (z i).re) eX) Zs Xs)
    (hY : List.Forall₂ (fun z Y => PhaseCellInterface.ErrorOn active
      (fun i => (packedIntervalRead q w a (cstream A w (packedInterval a L Y)++tailY) i).re)
      (fun i => (z i).im) eY) Zs Ys) :
    List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn active
      (packedIntervalRead q w a (cstream A w (packedInterval a L D)++tail)) z (eX+eY))
      Zs (pairedComponentFields Xs Ys) := by
  induction hX generalizing Ys with
  | nil => cases hY; exact .nil
  | @cons z X Zs Xs hx hX ih =>
    cases hY with
    | cons hy hY =>
      exact .cons (pairedPackedComponents_accuracy hA q w a L X _ active hfit hactive z eX eY
        tailX tailY tail hx hy) (ih _ hY)

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Consume the actual two published batches and return one complex packet per
replica. The retained N and output-row width generate the pairing count. -/
theorem pairPackedBatches_exec {replicas width count src buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    {s : ℕ} (a L w : ℕ) (hfit : a+L ≤ s)
    (Xs Ys : List (ZMod s → GaussianInt)) (hlen : Xs.length = Ys.length)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = Xs.length) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = ((Xs++Ys).map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ Xs.length*(16*(L*w)+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          (((pairedComponentFields Xs Ys).map (fun D => cstream A w (packedInterval a L D))).flatten++tail))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := pairComplexKey_exec (body := body) hreg hA Xs.length (L*w) w
    (Xs.map (packedInterval a L)).flatten (Ys.map (packedInterval a L)).flatten
    (by rw [packedBatch_length a L Xs hfit,packedBatch_length a L Ys hfit,hlen])
    (by rw [packedBatch_length a L Xs hfit]; ring) tail v S hreplicas hwidth
    (by simpa [cstream_flatten,List.map_append,List.flatten_append,List.map_map,Function.comp_def] using hsrc)
    hcount hbuf hsaved htmp
  refine ⟨v',n,hu,hn,?_⟩
  simpa only [packedBatch_pair a L hfit Xs Ys hlen,cstream_flatten,List.map_map,Function.comp_def] using he

/-- The numerical supplier returns one list of 2N outputs. Split that actual
list at N; the caller need not supply a decomposition or paired-output witness. -/
theorem pairPackedBatchHalves_exec {replicas width count src buf saved tmp : Fin T}
    (hreg : [replicas,width,count,src,buf,saved,tmp].Nodup) (hA : 4 ≤ A)
    {s : ℕ} (a L w N : ℕ) (hfit : a+L ≤ s)
    (Ds : List (ZMod s → GaussianInt)) (hDs : Ds.length = 2*N)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hreplicas : (S.R replicas).length = N) (hwidth : (S.R width).length = L*w)
    (hsrc : S.R src = (Ds.map (fun D => cstream A w (packedInterval a L D))).flatten++tail)
    (hcount : S.R count = []) (hbuf : S.R buf = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    let Gs := pairedComponentFields (Ds.take N) (Ds.drop N)
    Gs.length = N ∧
    ∃ v' n, v'.user = v.user ∧ n ≤ N*(16*(L*w)+9)+14 ∧
      Exec body (pairComplexKey replicas width count src buf saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R src
          ((Gs.map (fun D => cstream A w (packedInterval a L D))).flatten++tail))}) := by
  have htake : (Ds.take N).length = N := by simp [hDs]; omega
  have hdrop : (Ds.drop N).length = N := by simp [hDs]; omega
  refine ⟨by simp [pairedComponentFields,htake,hdrop],?_⟩
  obtain ⟨v',n,hu,hn,he⟩ := pairPackedBatches_exec (body := body) hreg hA a L w hfit
    (Ds.take N) (Ds.drop N) (htake.trans hdrop.symm) tail v S
    (hreplicas.trans htake.symm) hwidth (by simpa only [List.take_append_drop] using hsrc)
    hcount hbuf hsaved htmp
  exact ⟨v',n,hu,by simpa only [htake] using hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
