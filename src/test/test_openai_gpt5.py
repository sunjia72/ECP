import argparse
import json
import os
import sys

from openai import OpenAI


DEFAULT_MODEL = "gpt-5.4"
DEFAULT_PROMPT = "Write a one-sentence summary of why testing API access matters."



def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Send a test query to the OpenAI Responses API."
    )
    parser.add_argument(
        "--model",
        default=DEFAULT_MODEL,
        help=f"Model name to query. Default: {DEFAULT_MODEL}",
    )
    parser.add_argument(
        "--prompt",
        default=DEFAULT_PROMPT,
        help="Prompt to send to the model.",
    )

    return parser.parse_args()


def main() -> int:
    args = parse_args()

    api_key = os.getenv("OPENAI_API_KEY")
    if not api_key:
        print("OPENAI_API_KEY is not set.", file=sys.stderr)
        return 1

    client = OpenAI(api_key=api_key)

    request = {
        "model": args.model,
        "input": args.prompt,
    }
    if args.verbosity != "none":
        request["text"] = {"format": {"type": "text"}}

    response = client.responses.create(**request)

    print(response.output_text)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
