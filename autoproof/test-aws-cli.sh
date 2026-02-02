#!/bin/bash

# Test whether aws-cli works well.
MODEL_ID="us.anthropic.claude-3-5-sonnet-20241022-v2:0"

PROMPT="What is the capital of France?"
REQUEST_BODY=$(cat <<EOF
{
  "anthropic_version": "bedrock-2023-05-31",
  "max_tokens": 1024,
  "messages": [
    {
      "role": "user",
      "content": "$PROMPT"
    }
  ]
}
EOF
)

aws bedrock-runtime invoke-model --model-id "$MODEL_ID" --body "$REQUEST_BODY" --cli-binary-format raw-in-base64-out response.json
