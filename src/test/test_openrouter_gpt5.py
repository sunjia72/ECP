import argparse
import json
import os
import sys
from typing import Any, Dict

import requests


DEFAULT_MODEL = "openai/gpt-5.4"
DEFAULT_PROMPT = "Answer in exactly one short sentence: what is 2 + 2?"
OPENROUTER_CHAT_COMPLETIONS_URL = "https://openrouter.ai/api/v1/chat/completions"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Send a minimal OpenRouter smoke-test request to GPT-5.4."
    )
    parser.add_argument(
        "--model",
        default=DEFAULT_MODEL,
        help=f"OpenRouter model id. Default: {DEFAULT_MODEL}",
    )
    parser.add_argument(
        "--prompt",
        default=DEFAULT_PROMPT,
        help="Toy prompt to send to the model.",
    )

    parser.add_argument(
        "--max-completion-tokens",
        type=int,
        default=64,
        help="Maximum completion tokens for the test request. Default: 64.",
    )
    return parser.parse_args()


def build_payload(args: argparse.Namespace) -> Dict[str, Any]:
    payload: Dict[str, Any] = {
        "model": args.model,
        "messages": [
            {"role": "system", "content": "You are concise."},
            {"role": "user", "content": args.prompt},
        ],
        "temperature": 0,
        "max_completion_tokens": args.max_completion_tokens,
    }
    return payload


def build_headers(api_key: str) -> Dict[str, str]:
    headers = {
        "Authorization": f"Bearer {api_key}",
        "Content-Type": "application/json",
        "X-Title": os.getenv("OPENROUTER_X_TITLE", "OpenRouter smoke test"),
    }
    referer = os.getenv("OPENROUTER_HTTP_REFERER") or os.getenv("OPENROUTER_SITE_URL")
    if referer:
        headers["HTTP-Referer"] = referer

    return headers


def main() -> int:
    args = parse_args()

    api_key = os.getenv("OPENROUTER_API_KEY")
    if not api_key:
        print("OPENROUTER_API_KEY is not set.", file=sys.stderr)
        return 1

    payload = build_payload(args)
    headers = build_headers(api_key)

    try:
        response = requests.post(
            OPENROUTER_CHAT_COMPLETIONS_URL,
            headers=headers,
            json=payload,
            timeout=60,
        )
    except requests.RequestException as exc:
        print(f"OpenRouter request failed: {exc}", file=sys.stderr)
        return 1

    if not response.ok:
        print(f"OpenRouter request failed with HTTP {response.status_code}:", file=sys.stderr)
        print(response.text, file=sys.stderr)
        return 1

    try:
        data = response.json()
    except ValueError:
        print("OpenRouter request failed: response was not valid JSON.", file=sys.stderr)
        print(response.text, file=sys.stderr)
        return 1

    message = data["choices"][0]["message"]
    print(message.get("content", ""))

    usage = data.get("usage")
    if usage:
        print(json.dumps({"model": data.get("model"), "usage": usage}, indent=2))
    else:
        print(json.dumps({"model": data.get("model")}, indent=2))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
