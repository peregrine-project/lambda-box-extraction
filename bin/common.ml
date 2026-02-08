type verbose = Normal | Quiet | Verbose

type copts = {
  verbose: verbose;
  debug: bool;
  output_file: string option;
}
let mk_copts verbose debug output_file = {
  verbose;
  debug;
  output_file
}

type certicoq_opts = {
  cps: bool;
  c_args: int option;
  o_level: int option;
  prefix: string option;
  body_name: string option;
}

let mk_certicoq_opts cps c_args o_level prefix body_name = {
  cps;
  c_args;
  o_level;
  prefix;
  body_name;
}


type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option
