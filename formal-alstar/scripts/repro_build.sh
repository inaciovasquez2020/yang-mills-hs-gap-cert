#!/usr/bin/env bash
set -e

echo "==> Removing build artifacts"
rm -rf .lake

echo "==> Running clean build"
lake build

echo "==> Build complete"
