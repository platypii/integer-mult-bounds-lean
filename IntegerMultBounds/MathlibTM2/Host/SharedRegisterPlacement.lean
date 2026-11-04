module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Place shared ports in a retained caller bank and every other register in
private storage. Separation and injectivity are proved structurally once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
variable {N B T : ℕ}

def sharedRegisterPlacement (privateBank : Fin N → Fin T) (shared : Fin B → Fin T)
    (role : Fin N → Option (Fin B)) (i : Fin N) : Fin T :=
  match role i with
  | none => privateBank i
  | some j => shared j

theorem sharedRegisterPlacement_injective (privateBank : Fin N → Fin T)
    (hprivate : Function.Injective privateBank) (shared : Fin B → Fin T)
    (hshared : Function.Injective shared) (hoff : ∀ i j, privateBank i ≠ shared j)
    (role : Fin N → Option (Fin B))
    (hrole : ∀ i k j, role i = some j → role k = some j → i = k) :
    Function.Injective (sharedRegisterPlacement privateBank shared role) := by
  intro i k he
  cases hi : role i with
  | none =>
    cases hk : role k with
    | none => exact hprivate (by simpa only [sharedRegisterPlacement,hi,hk] using he)
    | some j => exact (hoff i j (by simpa only [sharedRegisterPlacement,hi,hk] using he)).elim
  | some j =>
    cases hk : role k with
    | none => exact (hoff k j (by simpa only [sharedRegisterPlacement,hi,hk] using he.symm)).elim
    | some l =>
      have hj : j = l := hshared (by simpa only [sharedRegisterPlacement,hi,hk] using he)
      exact hrole i k j hi (hj ▸ hk)

end IntegerMultBounds.MathlibTM2.Host
