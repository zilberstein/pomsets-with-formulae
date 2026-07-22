import Pom.Lpo.Linearization
import Pom.Order.Extension

open OmegaCompletePartialOrder Linearization

namespace Pomfin

noncomputable def lin (t : Type → Type) (α act test : Type)
    [Linearizable t α] [Bot (t α)]
    [Sem act α (t α)] [Sem test α (t Bool)]
    (p : Pomfin (Label act test)) : α → t α :=
  p.lift Lpofin.lin (fun _ _ ↦ Lpofin.lin_isomorphic)

lemma lin_monotone (t : Type → Type) (α act test : Type)
    [Linearizable t α]
    [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [PartialOrder act] [Sem act α (t α)]
    [PartialOrder test] [Sem test α (t Bool)] :
    Monotone (lin t α act test) :=
  Pomfin.lift_monotone Lpofin.lin_mono

lemma lin_mk {t : Type → Type} {X act test : Type}
    [Linearizable t X] [Bot (t X)]
    [Sem act X (t X)] [Sem test X (t Bool)]
    (α : Lpofin (Label act test)) :
    lin t X act test (mk α) = Lpofin.lin α := by
  unfold lin; exact Quotient.lift_mk _ _ _

end Pomfin

namespace Pom

noncomputable def lin {t : Type → Type} {α act test : Type}
    [Linearizable t α]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act α (t α)]
    [DCPO test] [Sem test α (t Bool)]
    (p : Pom (Label act test)) : α → t α :=
  p.ext _ (Pomfin.lin_monotone t α act test)

lemma lin_continuous {t : Type → Type} {α act test : Type}
    [Linearizable t α]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [ScottCompact act] [Sem act α (t α)]
    [DCPO test] [ScottCompact test] [Sem test α (t Bool)] :
    ωScottContinuous (Pom.lin : Pom (Label act test) → α → t α) :=
  ext_continuous (Pomfin.lin_monotone t α act test)

lemma lin_eq_fin {t : Type → Type} {α act test : Type}
    [Linearizable t α]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act α (t α)]
    [DCPO test] [Sem test α (t Bool)]
    (p : Pomfin (Label act test)) :
    lin p.to_pom = Pomfin.lin t α act test p := ext_eq_fin _ p

lemma lin_mk {t : Type → Type} {X act test : Type}
    [Linearizable t X]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [DCPO act] [Sem act X (t X)]
    [DCPO test] [Sem test X (t Bool)]
    (α : Lpo (Label act test)) :
    ((Pom.mk α).lin : X → t X) = ωSup {
      toFun n := (α.trunc n).lin
      monotone' _ _ hle :=  Lpofin.lin_mono (Lpo.trunc_mono (le_refl α) hle)
    } := by
  refine congrArg ωSup ?_; ext1; ext1 n; simp only [DFunLike.coe]
  rw [trunc_mk]; unfold Pomfin.lin
  conv => lhs; exact Quotient.lift_mk _ _ _

end Pom
