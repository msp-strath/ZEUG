module Command where

import Raw
import ProofState

command :: ProofState -> Raw -> ([String], Maybe ProofState)
command c r = (["Try doing something else."], Nothing)