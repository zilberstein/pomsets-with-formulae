import Pcol.Semantics.Lpo.Linearization
import Pcol.Semantics.Lpo.Operations.Seq

namespace Lpofin

open Lpo

variable {t : Type → Type} {α act test: Type}
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [∀ {β : Type}, Preorder (t β)]
    [Linearizable t] [Bot (t α)] [LawfulMonad t]

lemma nondet_congr {ι κ : Type} {f :ι → t α} {g : κ → t α}
    (e : ι ≃ κ) (h : f = g ∘ e) :
    Linearizable.nondet f = Linearizable.nondet g := by
  sorry

lemma lin_rec_seq
    {a b : Lpofin (Label act test)} {f : CopyFn a b}
    {s : Finset Node} :
    Lpo.lin_rec (t := t) (seq a b f) s =
    fun (st : α) ↦ bind (Lpo.lin_rec a (s ∩ a.nodes_finset) st) (Lpo.lin b) := by
  ext st; induction s using Finset.strongInduction with
    | H s hind =>
      conv => rhs; unfold lin_rec
      by_cases hemp : s ∩ a.nodes_finset = ∅
      · simp only [hemp, ↓reduceIte, pure_bind]
        sorry
      · have hemp' : s ≠ ∅ := by
          rintro rfl; apply hemp; exact Finset.empty_inter _
        unfold lin_rec; simp only [hemp', ↓reduceIte, hemp]
        have additivity {ι} {f : ι → t α} {g : α → t α} :
            Linearizable.nondet f >>= g = Linearizable.nondet (fun i ↦ f i >>= g) := sorry
        rw [additivity]; refine nondet_congr ?_ ?_
        · refine Equiv.setCongr ?_
          sorry
        · sorry



lemma lin_seq
    {a b : Lpofin (Label act test)} {f : CopyFn a b} :
    Lpo.lin (t := t) (seq a b f) =
    fun (st : α) ↦ bind (Lpo.lin a st) (Lpo.lin b) := by
  ext st; unfold lin
  have : a.nodes_finset = (a.seq b f).nodes_finset ∩ a.nodes_finset := by
    refine Finset.Subset.antisymm ?_ Finset.inter_subset_right
    refine Finset.subset_inter ?_ Finset.Subset.rfl
    refine Set.Finite.toFinset_mono Set.subset_union_left
  rw [this]; exact congrFun lin_rec_seq _

end Lpofin
