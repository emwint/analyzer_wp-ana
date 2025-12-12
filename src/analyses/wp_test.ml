open GoblintCil
open Analyses

module Spec : Analyses.Spec =
struct
  let name () = "wp_test"

  include Analyses.IdentityUnitContextsSpec

  module LiveVariableSet =  SetDomain.ToppedSet (Basetype.Variables) (struct let topname = "All variables" end)
  module D =  LiveVariableSet (*Set of program variables as domain*)

  let startstate v = D.bot()
  let exitstate v = D.bot()

end