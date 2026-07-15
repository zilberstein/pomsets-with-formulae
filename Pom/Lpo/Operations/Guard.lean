import Pom.Lpo.Operations.Par.Order

namespace Lpo

noncomputable def guard {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpo l}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥) : Lpo l :=
  par_gen hx hx' hd hroot (φ₁ := Form.literal x) (φ₂ := (Form.literal x).not)
    ⟨fun _ h ↦ h, Form.DependsOn.literal⟩
    ⟨fun _ h ↦ h, Form.DependsOn.literal.not⟩

lemma guard_monotone {l : Type} [PartialOrder l] [OrderBot l]
    {x : Node} {ℓ ℓ' : l} {α α' β β' : Lpo l}
    (hx₁ : x ∉ α'.nodes) (hx₂ : x ∉ β'.nodes) (hd : Disjoint α'.nodes β'.nodes)
    (hroot : ℓ ≠ ⊥)
    (hle : ℓ ≤ ℓ') (hle₁ : α ≤ α') (hle₂ : β ≤ β') :
    guard
      (fun h ↦ hx₁ (hle₁.nodes h))
      (fun h ↦ hx₂ (hle₂.nodes h))
      (hd.mono hle₁.nodes hle₂.nodes) hroot ≤
    guard hx₁ hx₂ hd (ne_bot_of_le_ne_bot hroot hle) :=
  par_monotone hx₁ hx₂ hd hroot _ _ hle hle₁ hle₂

end Lpo
