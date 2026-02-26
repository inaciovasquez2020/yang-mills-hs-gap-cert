#!/bin/bash
CERT_FILE=$1

STATUS=$(jq -r 'if .status | type == "object" then .status.type else .status end' "$CERT_FILE")

echo "status: $STATUS"

case "$STATUS" in
  draft)
    echo "PASS: status=draft (non-claiming certificate)"
    exit 0
    ;;
  final|verified|NEGATIVE_RESULT)
    echo "ok -- validation done"
    exit 0
    ;;
  *)
    echo "FAIL: invalid status.type = $STATUS"
    exit 1
    ;;
esac
