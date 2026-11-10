#!/bin/bash
# descend.sh k Bstart segundos semilla : baja B mientras el recocido encuentre solución
k=$1; B=$2; T=$3; seed=$4; N=$((k*k))
while true; do
  out=$(./sa $k $N $B $T $seed 2>/dev/null)
  echo "$out"
  case "$out" in *ENCONTRADO*H=*) B=$((B-1));; *) break;; esac
done
