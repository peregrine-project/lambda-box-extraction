
{ lib, mkCoqDerivation, which, coq
  , metarocq, ElmExtraction, RustExtraction
  , ceres, CertiCoq, verified-extraction
  , coq-primitive
  , version ? null }:

with lib; mkCoqDerivation {
  pname = "lambda-box-extraction";
  repo = "lambda-box-extraction";
  owner = "AU-COBRA";
  domain = "github.com";
  opam-name = "rocq-lambda-box-extraction";

  inherit version;
  defaultVersion = with versions; switch coq.coq-version [
  ] null;

  propagatedBuildInputs = [
    coq.ocamlPackages.cmdliner
    coq.ocamlPackages.findlib
    coq.ocamlPackages.dune_3
    metarocq
    ElmExtraction
    RustExtraction
    ceres
    CertiCoq
    verified-extraction
    coq-primitive
  ];

  mlPlugin = true;
  useDune = true;

  preBuild = ''
    make theory
  '';

  installPhase = ''
    runHook preInstall
    dune install --prefix=$out --libdir $OCAMLFIND_DESTDIR  rocq-lambda-box-extraction
    runHook postInstall
  '';

  meta = {
    ## Describe your package in one sentence
    # description = "";
    ## Kindly ask one of these people if they want to be an official maintainer.
    ## (You might also consider adding yourself to the list of maintainers)
    # maintainers = with maintainers; [ cohencyril siraben vbgl Zimmi48 ];
    ## Pick a license from
    ## https://github.com/NixOS/nixpkgs/blob/master/lib/licenses.nix
    # license = licenses.mit;
  };
}
