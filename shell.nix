{ pkgs ? import <nixpkgs> {} }:
(pkgs.callPackage ./. {}).overrideAttrs
  (attr: {
    buildInputs = with pkgs; [
      cabal-install
      hlint
    ];
  })
