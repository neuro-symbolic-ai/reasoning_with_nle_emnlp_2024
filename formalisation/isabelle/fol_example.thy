theory Scratch
imports Main

begin

typedecl entity
typedecl event

consts
  Consumer :: "entity ⇒ bool"
  Feed :: "event ⇒ bool"
  Agent :: "event ⇒ entity ⇒ bool"
  At :: "event ⇒ entity ⇒ bool"
  MoreThanOneTrophicLevel :: "entity ⇒ bool"
  Omnivore :: "entity ⇒ bool"
  Many :: "(entity ⇒ bool) ⇒ bool"

(* Explanation 1: Many consumers feed at more than one trophic level. *)
axiomatization where
  explanation_1: "∃x y e. x ≠ y ∧ Consumer x ∧ Consumer y ∧ 
                   (Feed e ∧ Agent e x ∧ At e z ∧ MoreThanOneTrophicLevel z) ∧
                   (Feed e ∧ Agent e y ∧ At e w ∧ MoreThanOneTrophicLevel w)"

(* Explanation 2: Omnivores are a type of consumer. *)
axiomatization where
  explanation_2: "∀x. Omnivore x ⟶ Consumer x"

theorem hypothesis:
  assumes asm: "Omnivore x"
  (* Hypothesis: Omnivores can feed at more than one trophic level. *)
  shows "∃x e. Omnivore x ⟶ (Feed e ∧ Agent e x ∧ At e y ∧ MoreThanOneTrophicLevel y)"
  using explanation_1 explanation_2 by blast
  

end
