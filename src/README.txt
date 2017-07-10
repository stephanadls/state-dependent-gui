Loading everything plus guide to code
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The file
   examples/GUIgeneric/loadAllRepository.agda

loads everything.


Installation
~~~~~~~~~~~~~~

You need to have as well the standard library installed
with a file std-lib.agda-lib in the src directory
containing the following (excluding the lines starting with --)

-- begin code --
name: standard-library
include: .
-- end code --

Add as well the path to this library file to the agda libraries file.

We type checked the library with the version of agda on github
   https://github.com/agda/agda
   (e.g., tested with ca1ab2b22a7a1d8a8740920c7885972f9dd81ed6)


HTML version
~~~~~~~~~~~~
An HTML version can be found at
  https://stephanadls.github.io/state-dependent-gui/html/GUIgeneric.loadAllRepository.html




COMPILATION / RUNNING GRAPHICS PROGRAMS
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


Details:

  - Install agda from git:

    git clone https://github.com/agda/agda.git

    sudo cabal update

    in the created directory

    sudo cabal install --global
    agda-mode setup

- Install Agda standard library version (latest master branch version)

  git clone https://github.com/agda/agda-stdlib

    (adaption of library files see below)

  - Install wxWidgets version 3.0.2
    https://www.wxwidgets.org/
    Follow the installation instructions in for the latest stable version
    ("Latest Stable Release: 3.0.2" not the development version)

    Follow the instructions in

    https://github.com/wxWidgets/wxWidgets/blob/v3.0.2/docs/readme.txt

    and use the installation instructions for gtk,
    with instructions in the downloaded version
    at  wxWidgets-3.1.0/docs/gtk/install.txt
    (easiest to follow instructions "The simplest case")

  - Install wxHaskell from github
    https://github.com/wxHaskell/wxHaskell
    (latest master branch version, tested with commit
    "db2a571300b5810a7dadfe117744e5b9389e0c9b"")

    Best is to clone
    https://github.com/wxHaskell/wxHaskell
    by using
    git clone https://github.com/wxHaskell/wxHaskell

    Then follow instructions at
    install.txt

    possibly replace  there
    cabal install
    by
    sudo cabal install

    if you do NOT have your haskell stuff in /home
    (thus if you have a global install directory for all users):
    sudo cabal install  --global
    or
    cabal install --global


  - Set up the agda library files:

The library files should work out of the box. if not,
then you have to add all the "*.agda-lib" in the repository to "~/.agda/libraries".
