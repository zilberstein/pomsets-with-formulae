import Pom.Lpo.Operations.Par.Defs
import Pom.Lpo.Order.FinApprox

namespace Lpo

lemma par_trunc {l : Type} [Preorder l] [OrderBot l] {x : Node} {ℓ : l} {α β : Lpo l}
    {φ₁ φ₂ : Form Node}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    {hroot : ℓ ≠ ⊥}
    {hφ₁ : Form.literal x ≤ φ₁ ∧ φ₁.DependsOn {x}}
    {hφ₂ : (Form.literal x).not ≤ φ₂ ∧ φ₂.DependsOn {x}}
    (n : ℕ) :
    (par_gen hx hx' hd hroot hφ₁ hφ₂).trunc (n + 1) =
    par_gen
      (by { intro h; apply hx; exact (α.trunc_le n).nodes h})
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot hφ₁ hφ₂ := by sorry

end Lpo
