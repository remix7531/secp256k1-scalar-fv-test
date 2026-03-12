# VST 2.16 for Rocq 9.0 — extends nixpkgs VST/default.nix with the
# missing version entry.  Once merged upstream this file can be removed.
{
  lib,
  mkCoqDerivation,
  coq,
  compcert,
  ITree,
  version ? null,
}:

mkCoqDerivation {
  pname = "coq${coq.coq-version}-VST";
  namePrefix = [ ];
  displayVersion.coq = false;
  owner = "PrincetonUniversity";
  repo = "VST";
  inherit version;

  defaultVersion = with lib.versions; lib.switch coq.coq-version [
    { case = range "9.0" "9.2"; out = "2.16"; }
  ] null;

  release."2.16".sha256 = "sha256-/IlFLiojtuENHE9d+j55Z2rYw5HUkltwVim75w/UFVE=";
  releaseRev = v: "v${v}";

  buildInputs = [ ITree ];
  propagatedBuildInputs = [ compcert ];

  preConfigure = ''
    patchShebangs util
  '';

  makeFlags = [
    "BITSIZE=64"
    "COMPCERT=inst_dir"
    "COMPCERT_INST_DIR=${compcert.lib}/lib/coq/${coq.coq-version}/user-contrib/compcert"
    "INSTALLDIR=$(out)/lib/coq/${coq.coq-version}/user-contrib/VST"
    "IGNORECOQVERSION=true"
    "IGNORECOMPCERTVERSION=true"
  ];

  postInstall = ''
    for d in msl veric floyd sepcomp progs64; do
      cp -r $d $out/lib/coq/${coq.coq-version}/user-contrib/VST/
    done
  '';

  meta = {
    description = "Verified Software Toolchain";
    homepage = "https://vst.cs.princeton.edu/";
    inherit (compcert.meta) platforms;
  };
}
