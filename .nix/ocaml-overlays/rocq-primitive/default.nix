{
  lib,
  fetchzip,
  buildDunePackage,
}:

buildDunePackage (finalAttrs: {
  pname = "rocq-primitive";
  version = "9.0.0";

  src = fetchzip {
    url = "https://github.com/peregrine-project/rocq-primitive/archive/refs/tags/${finalAttrs.version}.tar.gz";
    hash = "sha256-AGVYWIiAe/cmAffV6jDHc166yUg1zDFzUj6b1NvWyvk=";
  };

  meta = {
    homepage = "https://github.com/peregrine-project/rocq-primitive";
    description = "This library provides OCaml modules for primitive objects in Rocq.";
    license = lib.licenses.lgpl21;
    maintainers = with lib.maintainers; [ _4ever2 ];
  };
})
