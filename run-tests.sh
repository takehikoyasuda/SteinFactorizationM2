#!/bin/sh
set -eu

M2 --no-readline --stop -q tests/basic.m2
M2 --no-readline --stop -q tests/global-hom.m2
M2 --no-readline --stop -q tests/weighted.m2
M2 --no-readline --stop -q tests/conic-target.m2
M2 --no-readline --stop -q tests/mori-fiber-space.m2
M2 --no-readline --stop -q tests/blowup-line.m2

echo "Standard SteinFactorizationM2 tests passed."
echo "Run tests/blowup-twisted-cubic.m2 separately for the slower benchmark."
