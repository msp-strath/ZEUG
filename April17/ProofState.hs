------------------------------------------------------------------------------
-----                                                                    -----
-----     The Proof State                                                -----
-----                                                                    -----
------------------------------------------------------------------------------

module ProofState where

type ProofState = ()

initialProofState :: ProofState
initialProofState = ()

display :: ProofState -> [String]
display () =  -- art by Joan Stark
  ["            ___"
  ,"           |   |"
  ,"           |   '._   _"
  ,"           |      ``` '|"
  ,"       ____|           \\"
  ,"      `-.               |"
  ,"         \\ _           /"
  ,"          ` `\\       /`"
  ,"              \\   .'`"
  ,"        jgs    \\  \\ "
  ,"                '-;"
  ]

prompt :: ProofState -> String
prompt () = "/not/in/kansas"
