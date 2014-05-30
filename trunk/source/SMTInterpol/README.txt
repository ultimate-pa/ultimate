SMTInterpol in Ultimate
=======================

SMTInterpol is merged manually into Ultimate.  Here are the
necessary steps.

1. Checkout clean smtinterpol git repository.
   cd ...
   git clone https://github.com/juergenchrist/smtinterpol smtinterpol.git

2. Find out the last merged version by looking into Version.properties
   cd ultimate/source
   cat SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.properties

3. Create a patch for the changes from SMTInterpol/src and LibrarySMTLIB/src.
   cd .../sminterpol.git
   git diff <version-number> SMTInterpol/src LibrarySMTLIB/src >smtinterpol.diff
   cd ultimate/source
   patch -p0 < .../smtinterpol.diff

4. Update Version.properties.  The easiest way to do this is:
   cd .../smtinterpol.git
   ant
   cd ultimate/source/SMTInterpol/src
   unzip ../../smtinterpol.git/smtinterpol.jar \*Version.properties

5. Make sure you added all new files and deleted all old files.  Run

   diff -x.svn -r SMTInterpol/src smtinterpol.git/SMTInterpol/src
   diff -x.svn -r LibrarySMTLIB/src smtinterpol.git/LibrarySMTLIB/src

   it should list some files from ultimate/util, Versions.properties, 
   and the automatically build parser/lexer files and the parser build
   scripts which are slightly different for smtinterpol.

6. Do an svn status and check if only changes are in src subdirectory.
7. Check if everything works in Eclipse.
8. svn commit.  The log message should say (version can be found by 
   executing "git describe" in smtinterpol.git)

   Updated SMTInterpol to version 2.1-102-g04e1b50
   from https://github.com/juergenchrist/smtinterpol
