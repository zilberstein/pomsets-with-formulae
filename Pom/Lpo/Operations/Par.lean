import Pom.Lpo.Order
import Pom.Lpo.Operations.Par.Defs

namespace Lpo

noncomputable def par {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpo l}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥) : Lpo l :=
  par_gen hx hx' hd hroot (φ₁ := Form.true) (φ₂ := Form.true)
    ⟨fun _ _ ↦ True.intro, fun _ _ _ ↦ rfl⟩
    ⟨fun _ _ ↦ True.intro, fun _ _ _ ↦ rfl⟩

end Lpo
