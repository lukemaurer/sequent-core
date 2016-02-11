module Language.SequentCore.Contify where

import Language.SequentCore.Driver.Flags
import Language.SequentCore.Syntax

import CoreMonad

runContifyGently                :: SeqFlags -> SeqCoreProgram -> CoreM SeqCoreProgram
contifyGentlyInProgram          :: SeqCoreProgram -> SeqCoreProgram
contifyInTerm                   :: SeqCoreTerm -> SeqCoreTerm
contifyGentlyInTerm             :: SeqCoreTerm -> SeqCoreTerm
