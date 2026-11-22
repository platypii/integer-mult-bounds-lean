module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepMaterialize
public import IntegerMultBounds.MathlibTM2.M6.BitSweepAllocatedReturn

/-! Place the stage exit beside its recursive host and the fixed sweep register file. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover
open Shared50ModularControl (prime)

noncomputable section

inductive Register (t c : ℕ) where
  | recursive (i : Fin t)
  | chart (i : Fin c)
  | sweep (i : Fin tapes)
  | crop (i : Fin 12)
  deriving Fintype, DecidableEq

noncomputable abbrev size (t c : ℕ) := Fintype.card (Register t c)

noncomputable def place {t c : ℕ} {ι : Type} (f : ι → Register t c) (hf : Function.Injective f) :
    ι ↪ Fin (size t c) := (⟨f,hf⟩ : ι ↪ Register t c).trans (Fintype.equivFin _).toEmbedding

noncomputable def recursive (t c : ℕ) := place (t := t) (c := c) Register.recursive (fun _ _ => Register.recursive.inj)
noncomputable def chart (t c : ℕ) := place (t := t) (c := c) Register.chart (fun _ _ => Register.chart.inj)
noncomputable def sweep (t c : ℕ) := place (t := t) (c := c) Register.sweep (fun _ _ => Register.sweep.inj)
noncomputable def tmp (t c : ℕ) := (Fintype.equivFin (Register t c)) (.crop 0)

def cropReg {t c : ℕ} (fan : Fin (142081+2) ↪ Fin t) (slots : Fin 142081 → Fin c)
    (i : Fin 142081) (j : Fin 12) : Register t c :=
  if j = 0 then .recursive (fan (i.castAdd 2)) else if j = 1 then .chart (slots i) else .crop j

noncomputable def port {t c : ℕ} (fan : Fin (142081+2) ↪ Fin t) (slots : Fin 142081 → Fin c)
    (i : Fin 142081) := place (cropReg fan slots i) (by
  intro j k h
  unfold cropReg at h
  split_ifs at h <;> simp_all)

private theorem cropReg_apart {t c} (fan : Fin (142081+2) ↪ Fin t) (slots : Fin 142081 → Fin c)
    (inj : Function.Injective slots) (i k : Fin 142081) (ne : i ≠ k) (j : Fin 12) :
    cropReg fan slots i j ≠ cropReg fan slots k 0 ∧ cropReg fan slots i j ≠ cropReg fan slots k 1 := by
  simp [cropReg]
  split_ifs <;> simp [fan.injective.eq_iff,inj.eq_iff,ne]
  exact (Fin.castAddEmb 2).injective.ne ne

theorem placedStageExit_exec {w B K t Q : ℕ} {P U : Type}
    (fan : Fin (142081+2) ↪ Fin t) (fits : 215 ≤ Q) (hb : 0 < B) (hk : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    ∀ (leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K)))),
    leave.states ≤ Q → ∀ body : P → Pr P (size t leave.tapes) Q prime U,
    let crop := port fan leave.slots
    let output := owners.trans (sweep t leave.tapes)
    let scratch := tmp t leave.tapes
    ∃ code, ∀ x u S, HelperFan (fan.trans (recursive t leave.tapes)) (singleLabelBank (firstRowLabel w) x) S →
      ChartPrivateReady leave (embStk (chart t leave.tapes) S) → CropCounters (crop 0) (A*B) N K S →
      (∀ i z, readAt blank (S.L (crop i 1)) (S.R (crop i 1)) z = blank) →
      S.L scratch = [] → S.R scratch = [] → (∀ i, S.R (output i) = []) →
      ∃ z F l, Exec body code (mk u S) l (mk z F) ∧
        l ≤ 142081*(7021*(A*B)*(N*K)+6)+1 + (leave.cost*(leave.tapes+5)+6) + (142081*(8*(A*(B*K))+10)+1) ∧
        z.user = u.user ∧ (∀ i, F.R (output i) = List.ofFn fun j => SparseRoleCircuit.encode (leave.transform x i j)) ∧
        ∀ j, (∀ i, owners i ≠ j) →
          F.L (sweep t leave.tapes j) = S.L (sweep t leave.tapes j) ∧
          F.R (sweep t leave.tapes j) = S.R (sweep t leave.tapes j) := by
  intro A N leave room body crop output scratch
  have run := stageExitWords_exec (w := w) (B := B) (K := K) body crop
  let encode := Fintype.equivFin (Register t leave.tapes)
  have atPort i j : crop i j = encode (cropReg fan leave.slots i j) := rfl
  obtain ⟨code,execute⟩ := run (by
    intro i k j h d
    simp only [atPort,cropReg,h,d,ite_false]) (by
    intro i k ne j
    simp only [atPort,ne_eq,encode.injective.eq_iff]
    exact cropReg_apart fan leave.slots leave.slots_injective i k ne j)
    fits hb hk leave (chart t leave.tapes) room (fan.trans (recursive t leave.tapes)) output scratch
    (by intro i j; apply encode.injective.ne; change cropReg _ _ _ _ ≠ .crop 0
        unfold cropReg; split_ifs <;> simp [*])
    (by intro i; exact encode.injective.ne (fun h => by cases h))
    (by intro i h j; apply encode.injective.ne; change cropReg _ _ _ _ ≠ .sweep _
        unfold cropReg; split_ifs <;> simp)
    (by intro i j; exact encode.injective.ne (fun h => by cases h))
    (by intro i; exact encode.injective.ne (fun h => by cases h))
    (fun _ => rfl) (fun _ => rfl) (by
      intro j privateSlot i h
      apply encode.injective.ne
      change cropReg _ _ _ _ ≠ .chart _
      unfold cropReg; split_ifs <;> simp [privateSlot i])
  refine ⟨code,?_⟩
  intro x u S live ready counters blank left right fresh
  obtain ⟨z,F,l,exec,paid,user,words,off⟩ := execute x u S live ready counters blank left right fresh
  refine ⟨z,F,l,exec,paid,user,words,?_⟩
  intro j hj
  apply off
  · intro i h
    apply encode.injective.ne
    change cropReg _ _ _ _ ≠ .sweep _
    unfold cropReg; split_ifs <;> simp
  · intro h; exact encode.injective.ne (fun h => by cases h)
  · intro i; exact encode.injective.ne (fun h => hj i (Register.sweep.inj h))

end

end IntegerMultBounds.MathlibTM2.M6.BitNode.SweepFile.Exit
