{
  lib,
  mkRocqDerivation,
  rocq-elpi,
  HoTT,
  trocq,
}:

mkRocqDerivation {
  pname = "trocq-hott";
  inherit (trocq) version;

  buildFlags = [ "hott" ];

  doCheck = true;
  checkTarget = [ "test-hott" ];

  installTargets = [ "install-hott" ];

  propagatedBuildInputs = [
    rocq-elpi
    HoTT
  ];
}
