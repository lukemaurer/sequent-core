module Language.SequentCore.Contify where

import Language.SequentCore.Driver.Flags
import Language.SequentCore.Syntax

runContify          :: ContifySwitches -> SeqCoreProgram -> SeqCoreProgram
runContifyGently    :: SeqCoreProgram -> SeqCoreProgram
contifyInTerm       :: SeqCoreTerm -> SeqCoreTerm
contifyGentlyInTerm :: SeqCoreTerm -> SeqCoreTerm
