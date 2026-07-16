import Pom.Lpo.Isomorphism
import Pom.Lpo.Operations.Par.Defs

namespace Lpo

lemma par_isomorphic {l : Type} [Bot l] {x y : Node} {ℓ : l} {α α' β β' : Lpo l}
    {φ₁ φ₂ ψ₁ ψ₂ : Form Node}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes}
    {hy : y ∉ α'.nodes} {hy' : y ∉ β'.nodes}
    {hd : Disjoint α.nodes β.nodes}
    {hd' : Disjoint α'.nodes β'.nodes}
    {hroot : ℓ ≠ ⊥}
    {hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x}}
    {hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}}
    {hψ₁ : Form.literal y ≤ ψ₁ ∧ ψ₁.DependsOn {y}}
    {hψ₂ : (Form.literal y).not ≤ ψ₂ ∧ ψ₂.DependsOn {y}}
    (hα : α ≈ α') (hβ : β ≈ β') :
    par_gen hx hx' hd hroot hφ₁ hφ₂ ≈
    par_gen hy hy' hd' hroot hψ₁ hψ₂ := by sorry

end Lpo
