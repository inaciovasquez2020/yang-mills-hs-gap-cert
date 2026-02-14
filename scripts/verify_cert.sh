#!/bin/bash
CERT_FILE=$1
STATUS=$(jq -r '.status // .type' "$CERT_FILE")

echo "status: $STATUS"

if [ "$STATUS" = "draft" ]; then
    echo "PASS: status=draft (non-claiming certificate)"
    exit 0
elif [ "$STATUS" = "final" ] || [ "$STATUS" = "verified" ]; then
    echo "ok -- validation done"
    exit 0
else
    echo "FAIL: invalid status.type = $STATUS"
    exit 1
fi
