from typing import Optional
from pathlib import Path
import logging


class RefinementModel():
    def __init__(self, generative_model, critique_model,
                 prompt_dict: Optional[dict] = None):
        if prompt_dict is None:
            prompt_dict = {
                'generate explanation': 'get_explanation_prompt.txt',
                'refine logical error no premise':
                    'refine_soft_no_premise_prompt.txt',
                'refine logical error with premise':
                    'refine_soft_with_premise_prompt.txt'
            }
        self.generative_model = generative_model
        self.critique_model = critique_model
        self.logger = None
        self.prompt_dict = prompt_dict

    # setup logger
    def _setup_logger(self, data_name: str):
        log_dir = Path(f'logs/{data_name}')
        log_dir.mkdir(parents=True, exist_ok=True)
        logger = logging.getLogger(data_name)
        logger.setLevel(logging.INFO)

        file_handler = logging.FileHandler(log_dir / 'refinement.log')
        file_formatter = logging.Formatter('%(message)s')
        file_handler.setFormatter(file_formatter)
        logger.addHandler(file_handler)

        console_handler = logging.StreamHandler()
        console_handler.setFormatter(file_formatter)
        logger.addHandler(console_handler)

        return logger

    # use generative_model to generate explanaiton
    def _get_explanation(self, hypothesis: str,
                         premise: Optional[str] = None) -> str:
        premise_sentence = ('' if premise is None else
                            f'Provided Premise Sentence:\n{premise}\n')
        explanation = ''
        explanation = self.generative_model.generate(
            model_prompt_dir='refinement_model',
            prompt_name=self.prompt_dict['generate explanation'],
            hypothesis_sentence=hypothesis,
            premise_sentence=premise_sentence
        )
        return explanation

    def _refine_explanation(self, explanation: str,
                            hypothesis: str,
                            critique_output: Optional[dict] = None,
                            premise: Optional[str] = None) -> str:
        refined_explanations = ''

        # if the critique model is a hard critique model
        if self.critique_model.type == 'hard':
            self.prompt_dict['refine logical error with premise'] = 'refine_hard_with_premise_prompt.txt'
            self.prompt_dict['refine logical error no premise'] = 'refine_hard_no_premise_prompt.txt'

        # if the critique model is a soft critique model
        # the prompt dict is set to default

        # if the critique model is a hard critique model
        if self.critique_model.type == 'hard':
            if premise is not None:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine logical error with premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    logical_information=f'{critique_output["logical information"]}',
                    critique_output=f'Code:\n{critique_output["code"]}\n\nProof step that failed:\n{critique_output["error code"]}',
                    premise=f'Original premise sentence:\n{premise}',
                    numbered_list=True,
                    remove_number=True
                )
            else:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine logical error no premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    logical_information=f'{critique_output["logical information"]}',
                    critique_output=f'Code:\n{critique_output["code"]}\n\nProof step that failed:\n{critique_output["error code"]}',
                    numbered_list=True,
                    remove_number=True
                )
        # if the critique model is a soft critique model
        else:
            if premise is not None:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine logical error with premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    premise=f'Original premise sentence:\n{premise}',
                    numbered_list=True,
                    remove_number=True
                )
            else:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine logical error no premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    numbered_list=True,
                    remove_number=True
                )
        if (refined_explanations != '' and
           hypothesis.lower() not in refined_explanations.lower()):
            explanation = refined_explanations
        return explanation

    def refine(self, hypothesis: str, premise: Optional[str] = None,
               explanation: Optional[str] = None,
               data_name: str = 'example',
               iterative_times: int = 10) -> dict:

        #self.logger = self._setup_logger(data_name)
        # if premise or explanation is empty, set it to None
        premise = None if premise is None or premise.strip() == '' else premise
        explanation = (None if explanation is None or
                       explanation.strip() == '' else explanation)
        # if explanation is None, use generative_model to generate explanation
        if explanation is None:
            explanation = self._get_explanation(hypothesis, premise)

        for i in range(iterative_times):
            semantic_validity = False
            # start isabelle server
            print(f"\n================= Iteration Number {i} ==================\n")
            #self.logger.info('=========================================')
            #self.logger.info(f'current is iteration: {i}')
            #self.logger.info(f'Premise sentence: {premise}')
            print(f"Premise: {premise}")
            print(f"Hypothesis: {hypothesis}")
            print(f"Explanation: ")
            #self.logger.info(f'Hypothesis sentence: {hypothesis}')
            #self.logger.info('Explanatory sentences:')
            for k, sentence in enumerate(explanation.split('.'), 1):
                if sentence.strip():
                    #self.logger.info(f"{k}. {sentence.strip()}")
                    print((f"{k}. {sentence.strip()}"))
            #self.logger.info('---------------------------------')
            print("\n-------------- Verification and Refinement -------------------")

            #self.logger.info('critiqueing....')
            (semantic_validity,
             critique_output) = self.critique_model.critique(
                iteration_number=i,
                explanation=explanation,
                hypothesis=hypothesis,
                premise=premise
            )
            # if the critique model is a hard critique model
            print("\n-------------- 4) Results -------------------\n")
            if (self.critique_model.type == 'hard' and
               not critique_output['syntactic validity']):
                #self.logger.info('The critique model is a hard critique model')
                #self.logger.info('There is a syntax error in critique ouput')
                #self.logger.info('Go to next iteration.')
                #self.logger.info('---------------------------------')
                print("\nSyntacitc error found in the formalization!! Go to the next iteration...\n")
                print(f'Error:\n{critique_output["error code"]}')
                continue

            if semantic_validity:
                print("The explanation is logically valid!")
                break
            else:
                # if the explanation is not valid, refine the explanation
                print("No proof can be found!The explanation is not logically valid! Refinement...")
                print("\n-------------- 5) Refinement Feedback -------------------\n")
                print(f'Error:\n{critique_output["error code"]}')
                print(f'\nLogical information:\n{critique_output["logical information"]}')
                explanation = self._refine_explanation(
                    explanation, hypothesis,
                    critique_output, premise,
                )
                #self.logger.info('---------------------------------')
                print('\n-------------- 6) Refined Explanation -------------------\n')
                for i, sentence in enumerate(explanation.split('.'), 1):
                    if sentence.strip():
                        print(f"{i}. {sentence.strip()}")
                #self.logger.info('---------------------------------')
        result = {
            'semantic validity': semantic_validity,
            'premise': premise,
            'hypothesis': hypothesis,
            'explanation': explanation,
            'refined iteration': i,
            'critique output': critique_output
        }
        #self.logger.info(result)
        print("=====================================================")
        for entry in result:
            print(entry, result[entry])
        return result
