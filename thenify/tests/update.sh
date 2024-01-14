#!/bin/bash
for i in {0..6} ; do
  python3 ../thenify.py input${i}.txt >output${i}.txt
done
