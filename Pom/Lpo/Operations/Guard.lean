import Pom.Lpo.Operations.Par.Isomorphism
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
    {hx₁ : x ∉ α'.nodes} {hx₂ : x ∉ β'.nodes} {hd : Disjoint α'.nodes β'.nodes}
    {hroot : ℓ ≠ ⊥}
    (hle : ℓ ≤ ℓ') (hle₁ : α ≤ α') (hle₂ : β ≤ β') :
    guard
      (fun h ↦ hx₁ (hle₁.nodes h))
      (fun h ↦ hx₂ (hle₂.nodes h))
      (hd.mono hle₁.nodes hle₂.nodes) hroot ≤
    guard hx₁ hx₂ hd (ne_bot_of_le_ne_bot hroot hle) :=
  par_monotone hle hle₁ hle₂

lemma guard_isomorphic {l : Type} [Bot l] {x y : Node} {ℓ : l} {α α' β β' : Lpo l}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hy : y ∉ α'.nodes} {hy' : y ∉ β'.nodes}
    {hd : Disjoint α.nodes β.nodes}
    {hd' : Disjoint α'.nodes β'.nodes}
    {hroot : ℓ ≠ ⊥}
    (hα : α ≈ α') (hβ : β ≈ β') :
    guard hx hx' hd hroot ≈ guard hy hy' hd' hroot := by
  have ⟨e₁, hα⟩ := hα
  have ⟨e₂, hβ⟩ := hβ
  refine ⟨Equiv.par e₁ e₂ hx hx' hd hy hy' hd', ?_⟩
  conv => lhs; exact par_permute hy hy' hd' e₁ e₂
  congr
  · ext v; simp only [Form.permute, Form.literal, Form.image, Subtype.exists,
      Set.mem_singleton_iff, exists_and_right, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨rfl, _⟩, hv⟩; exact hv
    · intro hv; refine ⟨y, ⟨rfl, ?_⟩, hv⟩; rfl
  · ext v; simp only [Form.permute, Form.not, Form.literal, Form.image, Subtype.exists,
      Set.mem_singleton_iff, exists_and_right, Set.mem_setOf_eq, not_exists, not_and,
      forall_exists_index]
    constructor
    · intro h; exact h y rfl rfl
    · rintro h _ rfl _; exact h

end Lpo
