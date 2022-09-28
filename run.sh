#!/bin/bash

cwd=$(dirname $0)

pushd $cwd

if [ ! -d .venv ]; then
  python3 -m venv .venv
  source .venv/bin/activate
  pip install -r requirements
else
  source .venv/bin/activate
fi

python domainbinder
