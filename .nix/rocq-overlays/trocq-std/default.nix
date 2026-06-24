{
  lib,
  mkRocqDerivation,
  rocq-elpi,
  trocq,
}:

mkRocqDerivation {
  pname = "trocq-std";
  inherit (trocq) version;

  buildFlags = [ "std" ];

  doCheck = true;
  checkTarget = [ "test-std" ];

  installTargets = [ "install-std" ];

  propagatedBuildInputs = [
    rocq-elpi
  ];
}
