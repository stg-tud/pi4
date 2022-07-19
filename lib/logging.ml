let encoding_src =
  Logs.Src.create "pi4.encoding" ~doc:"Logs Pi4's encoding events"

let frontend_src =
  Logs.Src.create "pi4.frontend" ~doc:"Logs Pi4's frontend events"

let prover_src = Logs.Src.create "pi4.prover" ~doc:"Logs Pi4's prover events"

let prover_profile_src =
  Logs.Src.create "pi4.prover.profile" ~doc:"Logs Pi4's prover profiling events"

let ssa_src =
  Logs.Src.create "pi4.ssa" ~doc:"Logs Pi4's SSA transformation events"

let typechecker_src =
  Logs.Src.create "pi4.typechecker" ~doc:"Logs Pi4's typechecker events"

let cache_src =
  Logs.Src.create "pi4.cache" ~doc:"Logs Pi4's cache events"

let chomp_src = Logs.Src.create "pi4.chomp" ~doc:"Logs Pi4's chomp events"

let substitution_src = Logs.Src.create "pi4.substitution" ~doc:"Logs Pi4's substitution events"