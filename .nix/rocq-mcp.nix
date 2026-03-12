{ lib, python3Packages, fetchFromGitHub }:

let
  pytanque = python3Packages.buildPythonPackage {
    pname   = "pytanque";
    version = "0-unstable-2025-03-23";
    src = fetchFromGitHub {
      owner = "LLM4Rocq";
      repo  = "pytanque";
      rev   = "060e69ffd7c54982e3e796c9c55bd2fa79b484a9";
      hash  = "sha256-6VrxjL7vib8NUSzkveaFTGB2k4ysipTJzI6QgFEkKpA=";
    };
    pyproject = true;
    build-system = [ python3Packages.setuptools ];
    propagatedBuildInputs = with python3Packages; [
      typing-extensions
      requests
    ];
    doCheck = false;
  };
in
python3Packages.buildPythonPackage {
  pname   = "rocq-mcp";
  version = "0.1.0";
  src = fetchFromGitHub {
    owner = "LLM4Rocq";
    repo  = "rocq-mcp";
    rev   = "0.1.0";
    hash  = "sha256-EO7M6x/rboC41aYcyQbcJymqlYbIxir2P9Ib1CIO3kE=";
  };
  pyproject = true;
  build-system = [ python3Packages.setuptools ];
  propagatedBuildInputs = with python3Packages; [
    mcp
    pytanque
  ];
  doCheck = false;
}
