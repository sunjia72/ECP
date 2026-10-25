from typing import Any, Dict, Tuple

from src.ecp.openai_utils import call_llm_text_with_stats
from src.ecp.utils import (
    parse_lean_in_delimiter,
    verify_answer_admissibility,
    verify_answer_syntax,
)

# We keep the Agent class for reference but do not use its __init__ in subclasses.
class Agent:
    """Base class: keeps prompts, model info and an interaction log."""
    def __init__(self, model: str = "gpt-5-mini"):
        self.model = model
        self.history =  ""

    
class Conjecturer(Agent):
    """Injects a Lean answer into an existing formal statement."""
    def __init__(
        self,
        filename: str,
        model: str = "gpt-5-mini",
        enable_mcp: bool = False,
    ):
        super().__init__(model)
        self.filename = filename
        self.enable_mcp = enable_mcp
        with open("data/prompts/conjecturer_formal.txt", encoding="utf-8") as f:
            self.system_prompt = f.read()
        with open("data/prompts/conjecturer_formal_refiner.txt", encoding="utf-8") as f:
            self.system_prompt_refiner = f.read()
        with open("data/prompts/conjecturer_formal_mcp.txt", encoding="utf-8") as f:
            self.system_prompt_mcp = f.read()
        self.answer_construction_stats: Dict[str, Any] = self._empty_answer_construction_stats()
        self.last_error = ""
        self.last_answer = "Error"

    @staticmethod
    def _empty_answer_construction_stats() -> Dict[str, Any]:
        return {
            "runtime_sec": 0.0,
            "output_tokens": 0,
            "tool_calls": 0,
            "api_calls": 0,
            "llm_calls": 0,
        }

    def _accumulate_llm_stats(self, llm_stats: Dict[str, Any]) -> None:
        if not isinstance(llm_stats, dict):
            return
        self.answer_construction_stats["runtime_sec"] += float(llm_stats.get("runtime_sec", 0.0) or 0.0)
        self.answer_construction_stats["output_tokens"] += int(llm_stats.get("output_tokens", 0) or 0)
        self.answer_construction_stats["tool_calls"] += int(llm_stats.get("tool_calls", 0) or 0)
        self.answer_construction_stats["api_calls"] += int(llm_stats.get("api_calls", 0) or 0)
        self.answer_construction_stats["llm_calls"] += 1

    def get_answer_construction_stats(self) -> Dict[str, Any]:
        stats = dict(self.answer_construction_stats)
        stats["runtime_sec"] = round(float(stats.get("runtime_sec", 0.0)), 6)
        return stats


    def _build_prompt_cot(
        self,
        formal_statement: str,
        expected_answer_type: str,
    ) -> str:
        prompt = self.system_prompt + f"Formal Problem Statement: {formal_statement}. "
        if expected_answer_type:
            prompt += f"Answer Type: {expected_answer_type}. "
        return prompt

    def _build_prompt_mcp(
        self,
        formal_statement: str,
        expected_answer_type: str,
    ) -> str:
        prompt = self.system_prompt_mcp + f"Formal Problem Statement: {formal_statement}. "
        if expected_answer_type:
            prompt += f"Answer Type: {expected_answer_type}. "
        return prompt

    def conjecture_answer(
        self, formal_statement: str, expected_answer_type: str
    ) -> str:
        # CoT == MCP with tools disabled
        prompt = self._build_prompt_cot(
            formal_statement, expected_answer_type
        )
        reply, llm_stats = call_llm_text_with_stats(prompt, model=self.model, allow_tools=False)
        self._accumulate_llm_stats(llm_stats)
        self.history += f"[conjecture_answer]\n{prompt}\n{reply}\n"
        answer = parse_lean_in_delimiter(reply)
        self.last_answer = answer

        return answer

    def conjecture_answer_mcp(
        self, formal_statement: str, expected_answer_type: str
    ):
        prompt = self._build_prompt_mcp(formal_statement, expected_answer_type)
        reply, llm_stats = call_llm_text_with_stats(prompt, model=self.model, allow_tools=True)
        self._accumulate_llm_stats(llm_stats)
        self.history += f"[conjecture_answer_mcp]\n{prompt}\n{reply}\n"
        answer = parse_lean_in_delimiter(reply)
        if "abbrev" in answer and ":=" in answer:
            idx = answer.index(":=")
            answer = answer[idx + 2 :]
        self.last_answer = answer
        return answer
    

    def refine_answer(
        self,
        formal_statement: str,
        current_answer: str,
        error: str,
        expected_answer_type: str,
    ) -> str:
        prompt = (
            self.system_prompt_refiner
            + "\n\n"
            + "You will refine a Lean answer for the following formal problem.\n\n"
            + f"Formal Problem Statement:\n{formal_statement}\n\n"
            + "Current proposed answer:\n"
            + f"{current_answer}\n\n"
            + "Lean error message:\n"
            + f"{error}\n\n"
            + "Expected answer type:\n"
            + f"{expected_answer_type}\n"
        )

        reply, llm_stats = call_llm_text_with_stats(
            prompt,
            model=self.model,
            allow_tools=False,
        )
        self._accumulate_llm_stats(llm_stats)

        self.history += f"[refine_answer] {prompt}\n{reply}"
        answer = parse_lean_in_delimiter(reply)
        self.last_answer = answer

        return answer
    def execute_formalization(self, answer, verifier_checker_info) -> Tuple[bool, str]:
        if not answer or ('abbrev' in answer):
            return False, 'Unable to parse answer. Make sure you include the answer in delimiter <<< >>> such as <<<1>>>. '
        syntax_correct, syntax_error_message = verify_answer_syntax(verifier_checker_info['header'],answer,verifier_checker_info['answer_type'])
        if not syntax_correct:
            return False, f"The answer has syntax error: {syntax_error_message}"
        admissible = verify_answer_admissibility(answer, verifier_checker_info)
        if not admissible:
            return False, (
                "Your answer is not simplified enough. Please give a more canonical simple Lean expression"
            )
        return True, ''



    def conjecture_answer_loop(
        self,
        formal_statement: str,
        verifier_checker_info,
        max_attempt: int = 5,
    ) -> Tuple[str, bool]:
        self.answer_construction_stats = self._empty_answer_construction_stats()
        self.last_error = ""
        self.last_answer = "Error"
        if self.enable_mcp:
            answer = self.conjecture_answer_mcp(
            formal_statement,  verifier_checker_info['answer_type']
        )
        else:
            answer = self.conjecture_answer(
                formal_statement, verifier_checker_info['answer_type']
            )


        ok, err = self.execute_formalization(answer,verifier_checker_info)
        self.last_error = err

        for _ in range(1, max_attempt):
            if ok:
                break
            answer = self.refine_answer(
                formal_statement,
                answer,
                err,
                verifier_checker_info['answer_type'],
            )

            ok, err = self.execute_formalization(answer,verifier_checker_info)
            self.last_error = err
        return answer, ok
    
