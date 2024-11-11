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

definition Large :: "entity set ⇒ bool" where
  "Large S ≡ card S > 2" 

definition Consumers :: "entity set" where
  "Consumers ≡ { x. Consumer x }"

definition ConsumersFeedingAtMultipleLevels :: "entity set" where
  "ConsumersFeedingAtMultipleLevels ≡
     { x. Consumer x ∧ (∃ e z. Feed e ∧ Agent e x ∧ At e z ∧ MoreThanOneTrophicLevel z) }"

(* Explanation 1: Many consumers feed at more than one trophic level. *)
axiomatization where
  explanation_1: "Large ConsumersFeedingAtMultipleLevels"

(* Explanation 2: Omnivores are a type of consumer. *)
axiomatization where
  explanation_2: "∀x. Omnivore x ⟶ Consumer x"

theorem hypothesis:
  assumes asm: "∀x. Omnivore x"
  shows "∃ e x z. Feed e ∧ Agent e x ∧ At e z ∧ MoreThanOneTrophicLevel z"
  by (smt (verit, best) ConsumersFeedingAtMultipleLevels_def Large_def bot_nat_0.extremum card.empty empty_Collect_eq explanation_1 linorder_not_less)

end
