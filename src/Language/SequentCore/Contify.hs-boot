module Language.SequentCore.Contify where

import Language.SequentCore.Syntax

runContify, runContifyGently       :: SeqCoreProgram -> SeqCoreProgram
contifyInTerm, contifyGentlyInTerm :: SeqCoreTerm -> SeqCoreTerm