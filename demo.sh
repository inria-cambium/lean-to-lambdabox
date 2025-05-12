#!/bin/zsh
lake exe lean_to_lambdabox | tee >(coqc -Q theories LeanToLambdaBox -w "-extraction-reserved-identifier" theories/deserialize_and_pp.v)
