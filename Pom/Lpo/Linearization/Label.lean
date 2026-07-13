import Mathlib.Order.WithBot

import DomainTheory.DCPO

inductive Label (act : Type) (test : Type)
  | bot : Label act test
  | fork : Label act test
  | act : act → Label act test
  | test : test → Label act test

namespace Label

variable {act test : Type}

def isAct (ℓ : Label act test) : Prop :=
  match ℓ with
  | Label.act _ => True
  | _ => False

def isTest (ℓ : Label act test) : Prop :=
  match ℓ with
  | Label.test _ => True
  | _ => False

end Label

instance {act test : Type} : Bot (Label act test) where
  bot := Label.bot

instance {act test : Type} [LE act] [LE test] : LE (Label act test) where
  le l1 l2 :=
    match l1 with
    | Label.bot => True
    | Label.fork => l2 = Label.fork
    | Label.act a =>
      match l2 with
      | Label.act a' => a ≤ a'
      | _ => False
    | Label.test b =>
      match l2 with
      | Label.test b' => b ≤ b'
      | _ => False

lemma lab_is_act_le {act test : Type} {a : act} {l : Label act test}
    [Preorder act] [Preorder test]
    (hle : Label.act a ≤ l) :
    ∃ a', l = Label.act a' ∧ a ≤ a' := by
  cases l <;> (try contradiction); exact ⟨_, rfl, hle⟩

lemma lab_is_test_le {act test : Type} {b : test} {l : Label act test}
    [Preorder act] [Preorder test]
    (hle : Label.test b ≤ l) :
    ∃ b', l = Label.test b' ∧ b ≤ b' := by
  cases l <;> (try contradiction); exact ⟨_, rfl, hle⟩

lemma lab_is_fork_le {act test : Type} {l : Label act test}
    [LE act] [LE test]
    (hle : Label.fork ≤ l) :
    l = Label.fork := by
  cases l <;> (try contradiction); rfl

instance {act test : Type} [LE act] [LE test] : OrderBot (Label act test) where
  bot_le _ := True.intro

instance {act test : Type} [Preorder act] [Preorder test] : Preorder (Label act test) where
  le_refl := by intro l; cases l <;> simp only [LE.le, Std.le_refl]
  le_trans := by {
    intro l₁ l₂ l₃ h12 h23; simp only [LE.le]
    match l₁ with
    | Label.bot => simp
    | Label.fork =>
        simp only [LE.le] at h12; simp only [LE.le, h12] at h23
        exact h23
    | Label.act a =>
        rcases lab_is_act_le h12 with ⟨a₂, hl₂, ha₂⟩; subst hl₂
        rcases lab_is_act_le h23 with ⟨a₃, hl₃, ha₃⟩; subst hl₃
        exact le_trans ha₂ ha₃
    | Label.test b =>
        rcases lab_is_test_le h12 with ⟨b₂, hl₂, hb₂⟩; subst hl₂
        rcases lab_is_test_le h23 with ⟨b₃, hl₃, hb₃⟩; subst hl₃
        exact le_trans hb₂ hb₃
  }

instance {act test : Type} [PartialOrder act] [PartialOrder test] :
    PartialOrder (Label act test) where
  le_antisymm l₁ l₂ h12 h21 := by {
    cases l₁ <;> cases l₂ <;>
      simp only [LE.le, reduceCtorEq, Label.act.injEq, Label.test.injEq] at *
    · exact le_antisymm h12 h21
    · exact le_antisymm h12 h21
  }

lemma label_dset {act test : Type} [Preorder act] [Preorder test] (d : DSet (Label act test)) :
    (∀ ℓ ∈ d, ℓ = ⊥ ∨ ℓ = Label.fork) ∨
    (∀ ℓ ∈ d, ℓ = ⊥ ∨ ℓ.isAct) ∨
    (∀ ℓ ∈ d, ℓ = ⊥ ∨ ℓ.isTest) := by
  have ⟨ℓ, hℓ⟩ := d.nonempty; cases ℓ with
  | bot => sorry
  | fork =>
    left; intro ℓ' hℓ'
    have ⟨z, _, hz, hle⟩ := d.directed _ hℓ _ hℓ'
    rcases lab_is_fork_le hz with rfl
    cases ℓ' <;> try contradiction
    · left; rfl
    · right; rfl
  | act a =>
    right; left; intro ℓ' hℓ'
    have ⟨z, _, hz, hle⟩ := d.directed _ hℓ _ hℓ'
    rcases lab_is_act_le hz with ⟨_, rfl, hle⟩
    cases ℓ' <;> try contradiction
    · left; rfl
    · right; trivial
  | test b =>
    right; right; intro ℓ' hℓ'
    have ⟨z, _, hz, hle⟩ := d.directed _ hℓ _ hℓ'
    rcases lab_is_test_le hz with ⟨_, rfl, hle⟩
    cases ℓ' <;> try contradiction
    · left; rfl
    · right; trivial

def to_act_dset {act test : Type} [Preorder act] [Preorder test] (d : DSet (Label act test)) :
    DSet (WithBot act) := {
  val := (Option.some '' { a | Label.act a ∈ d }).insert ⊥
  property := by
    constructor
    · intro x hx y hy
      rcases Set.mem_insert_iff.mp hx with rfl | ⟨a₁, ha₁, rfl⟩ <;>
        rcases Set.mem_insert_iff.mp hy with rfl | ⟨a₂, ha₂, rfl⟩
      · exact ⟨⊥, hx, le_refl _, le_refl _⟩
      · exact ⟨some a₂, hy, bot_le, le_refl _⟩
      · exact ⟨some a₁, hx, le_refl _, bot_le⟩
      · have ⟨ℓ, hℓ, hle₁, hle₂⟩ := d.directed _ ha₁ _ ha₂
        obtain ⟨a, rfl, _⟩ := lab_is_act_le hle₁
        refine ⟨a, ?_, WithBot.coe_le_coe.mpr hle₁, WithBot.coe_le_coe.mpr hle₂⟩
        exact Set.mem_insert_of_mem _ ((Set.mem_image _ _ _).mpr ⟨a, hℓ, rfl⟩)
    · exact Set.insert_nonempty _ _
}

instance {act test : Type} [DCPO act] [DCPO test] : DCPO (Label act test) where
  dSup d := sorry
  -- match label_dset d with
  -- | Or.inl _ => sorry
  -- | Or.inr (Or.inl _) => sorry
  lubOfDirected := sorry
