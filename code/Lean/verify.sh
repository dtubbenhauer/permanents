#!/bin/sh
set -eu
cd "$(dirname "$0")"
for path in BlockPermanents/*.lean; do
  module=${path##*/}
  module=${module%.lean}
  if ! grep -Fqx "import BlockPermanents.$module" BlockPermanents.lean; then
    echo "Missing project module in BlockPermanents.lean: $module" >&2
    exit 1
  fi
done
lake build
lake env lean Audit.lean
