#!/bin/bash
cd "$(dirname "$0")"
echo ""
echo "  Starting the KARN battle server..."
echo ""
if ! command -v node >/dev/null 2>&1; then
  echo "  ❌ Node.js is not installed."
  echo ""
  echo "  Download it from  https://nodejs.org  (choose the LTS version),"
  echo "  install it, then double-click this file again."
  echo ""
  read -p "  Press Enter to close..."
  exit 1
fi
node server.js
read -p "  Server stopped. Press Enter to close..."
