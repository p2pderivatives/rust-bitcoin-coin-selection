#!/bin/bash
while :
do
  if cargo test proptest ; then
    echo "success"
  else
    echo "fail"
    break
  fi
done
