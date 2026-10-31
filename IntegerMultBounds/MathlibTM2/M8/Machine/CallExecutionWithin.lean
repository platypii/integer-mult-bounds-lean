module

public import IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecutionWithin
public import IntegerMultBounds.Machine.HoareHeadChange

/-! Stage-1 call workspace shares the endpoint proof's physical boundary
contracts. Recovery is bounded backward from the known parent post-bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Implementation (commonCount implementation widthSlot pcStack)
open Control
open BaseExecution (entryConfig)
open SharedBankStageInput (raw)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveViewedAction (Data)
variable {k b : ℕ} {v : Descriptor}

omit [Net] in
private theorem boundary_allowance (E R V : ℕ) (hV : 0 < V) :
    E*V+1 ≤ 2*(E+R+2)*V ∧ 2*(R*V+1) ≤ 2*(E+R+2)*V := by
  rw [show 2*(E+R+2)*V = 2*(E*V)+2*(R*V)+4*V by ring]
  constructor <;> omega

theorem call_jump_within (capacity : Fintype.card PC ≤ 2^k) (site : Site)
    (w : Wire) (i j : Fin Machine.width) (hic : pieces[site] = .call w i j)
    (before entered returned after : Tapes commonCount prime) (E C R : ℕ)
    (he : HoareTime (block capacity widthSlot pcStack (implementation k) (.piece site)).program
      (· = raw before (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes)
      (· = raw entered (block capacity widthSlot pcStack (implementation k) (.piece site)).tapes) E)
    (hr : HoareTime (block capacity widthSlot pcStack (implementation k) (.recover site)).program
      (· = raw returned (block capacity widthSlot pcStack (implementation k) (.recover site)).tapes)
      (· = raw after (block capacity widthSlot pcStack (implementation k) (.recover site)).tapes) R)
    (lo hi : ℤ)
    (hc : ∃ n ≤ C, RunWithin (Control.program capacity widthSlot pcStack (implementation k))
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
      (entryConfig capacity .guard entered) (entryConfig capacity (.recover site) returned))
    (hbefore : ∀ j, lo+(E+1 : ℕ) ≤ (raw before (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
      (raw before (tapeCount capacity widthSlot pcStack (implementation k))).head j+(E+1 : ℕ) ≤ hi)
    (hafter : ∀ j, lo+(2*(R+1) : ℕ) ≤ (raw after (tapeCount capacity widthSlot pcStack (implementation k))).head j ∧
      (raw after (tapeCount capacity widthSlot pcStack (implementation k))).head j+(2*(R+1) : ℕ) ≤ hi) :
    ∃ n ≤ E+C+R+2, RunWithin (Control.program capacity widthSlot pcStack (implementation k))
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
      (entryConfig capacity (.piece site) before) (entryConfig capacity (successor site) after) := by
  obtain ⟨ne,hne,hte⟩ := BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
    (.piece site) .guard before entered E he (call_edge capacity widthSlot pcStack _ site w i j hic)
  obtain ⟨nc,hnc,htc⟩ := hc
  obtain ⟨nr,hnr,htr⟩ := BlockExecution.block_jump capacity widthSlot pcStack (implementation k)
    (.recover site) (successor site) returned after R hr (recover_edge capacity widthSlot pcStack _ site)
  have hwe := RunWithin.heads_of_run_le hte hne lo hi hbefore
  have hwr := RunWithin.heads_of_run_post_le htr hnr lo hi hafter
  exact ⟨ne+nc+nr,by omega,(hwe.trans htc).trans hwr⟩

/-- One call reserves room for its boundary work and the entered child's allowance. -/
def callReserve (D k : ℕ) (w : Wire) (i j : Fin Machine.width) : ℕ :=
  max (2*overhead k (.call w i j))
    (D+(88*(CallLayout.parked w).length+51884+RecursiveRoleChildCallSetup.constant Machine.width k))

/-- Fixed boundary work adds once to the child coefficient. -/
theorem callReserve_le (D k : ℕ) (w : Wire) (i j : Fin Machine.width) :
    callReserve D k w i j ≤ D+2*overhead k (.call w i j) := by
  dsimp only [callReserve,overhead]
  omega

/-- The outer row split absorbs the call boundary without increasing the
recursive coefficient. Node offsets are charged on parent volume. -/
theorem callReserve_shrink (D A B V R k : ℕ) (w : Wire) (i j : Fin Machine.width)
    (hboundary : 2*overhead k (.call w i j) ≤ B)
    (hhalf : 2*R ≤ V) (hD : 2*A+B ≤ D) :
    A*V+callReserve D k w i j*R ≤ D*V := by
  have hc := Nat.mul_le_mul_right R ((callReserve_le D k w i j).trans
    (Nat.add_le_add_left hboundary D))
  have hd := Nat.mul_le_mul_right V hD
  have hh := Nat.mul_le_mul_left (D+B) hhalf
  nlinarith only [hc,hd,hh]

variable (capacity : Fintype.card PC ≤ 2^k) (hw : v.width=Machine.width*b)
  (hp : v.Positive) (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs)
  (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime)

include hp hv hw in
theorem call_actual_within (site : Site) (w : Wire) (i j : Fin Machine.width)
    (hic : pieces[site] = .call w i j) (data : Data payloadCount v)
    (out : Fin (volume prime v) → Fin 4) (hio : data io = fun _ => blank)
    (hf : ∀ z, p ≤ z → f z = blank) (C D : ℕ) (lo hi : ℤ)
    (hbank : ∀ z, lo+(callReserve D k w i j*volume prime v : ℕ) ≤
        (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
      (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head z+
        (callReserve D k w i j*volume prime v : ℕ) ≤ hi)
    (childTrace : ∀ ch : Fin 6 → List Bool,
      RecursiveDimensionBank.Headers (RecursiveInterchangeLayout.child prime 1 b v i j) ch →
      let entered := RecursiveCallProtocol.childBank
        (RecursiveCallProtocol.entered (CallLayout.parked w) (wireSlot w) io (volume prime v)
          (dataBank hs f p node st data)) ch
        (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
        (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site))
      (∀ z, lo+(D*volume prime v : ℕ) ≤ (raw entered (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
        (raw entered (tapeCount capacity widthSlot pcStack (implementation k))).head z+(D*volume prime v : ℕ) ≤ hi) →
      ∃ n ≤ C, RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity .guard entered)
        (entryConfig capacity (.recover site) (SharedPlacementAlphabet.setTape
          (RecursiveCallProtocol.entered (CallLayout.parked w) (wireSlot w) io (volume prime v)
            (dataBank hs f p node st data))
          (RecursiveCallBank.role (u := 1+(1+0)) io).val (RecursiveShiftRoleBank.source out) 0))) :
    ∃ n ≤ actualCallBound (v := v) k C w i j,
      RunWithin (Control.program capacity widthSlot pcStack (implementation k))
        (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) n
        (entryConfig capacity (.piece site) (dataBank hs f p node st data))
        (entryConfig capacity (successor site) (dataBank hs f p node st (Function.update data (wireSlot w) out))) := by
  obtain ⟨ch,hch,he,hr⟩ := call_contracts capacity hw hp hs hv f p node st site w i j hic data out hio hf
  let V := volume prime v
  let E := 88*(CallLayout.parked w).length+51884+RecursiveRoleChildCallSetup.constant Machine.width k
  let R := 92*(CallLayout.parked w).length+51883
  let entered := RecursiveCallProtocol.childBank
    (RecursiveCallProtocol.entered (CallLayout.parked w) (wireSlot w) io V
      (dataBank hs f p node st data)) ch
    (node.append ((SharedBank.empty 1 prime).append (SharedBank.empty 0 prime)))
    (RecursiveChildCallSetup.savedStacks hs st (returnCode capacity site))
  have hV : 0 < V := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  have hb := boundary_allowance E R V hV
  have hl : 2*(E+R+2)*V ≤ callReserve D k w i j*V :=
    Nat.mul_le_mul_right V (le_max_left _ _)
  have hchildBudget : D*V+E*V ≤ callReserve D k w i j*V := by
    have h := Nat.mul_le_mul_right V (show D+E ≤ callReserve D k w i j from le_max_right _ _)
    rwa [Nat.add_mul] at h
  have hp := SharedBankFamily.realizes (block capacity widthSlot pcStack (implementation k))
    (.piece site) (dataBank hs f p node st data) entered (E*V) he
  have hmargin : ∀ z, lo+(D*V : ℕ) ≤ (raw entered (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
      (raw entered (tapeCount capacity widthSlot pcStack (implementation k))).head z+(D*V : ℕ) ≤ hi := by
    intro z
    have hh := hp.head_change z
    change (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head z-(E*V : ℕ) ≤
      (raw entered (tapeCount capacity widthSlot pcStack (implementation k))).head z ∧
      (raw entered (tapeCount capacity widthSlot pcStack (implementation k))).head z ≤
        (raw (dataBank hs f p node st data) (tapeCount capacity widthSlot pcStack (implementation k))).head z+(E*V : ℕ) at hh
    have h := hbank z
    dsimp only [V] at hchildBudget hh ⊢
    omega
  obtain ⟨n,hn,hw⟩ := call_jump_within capacity site w i j hic _ _ _ _ _ C _ he hr lo hi
    (childTrace ch hch hmargin)
    (fun z => by
      have h := hbank z
      have he := hb.1.trans hl
      dsimp only [E, V] at he
      change lo+_ ≤ (raw (dataBank hs f p node st data) _).head z ∧
        (raw (dataBank hs f p node st data) _).head z+_ ≤ hi
      omega)
    (fun z => by
      rw [dataBank_head_eq hs f p node st _ (Function.update data (wireSlot w) out) data]
      have h := hbank z
      have hr := hb.2.trans hl
      dsimp only [R, V] at hr
      omega)
  exact ⟨n,hn,hw⟩

end
end IntegerMultBounds.MathlibTM2.M8.Machine.PieceExecution
