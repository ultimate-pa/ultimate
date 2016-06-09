SMTInterpol in Ultimate
=======================

SMTInterpol is merged manually into Ultimate.  Here are the
necessary steps.

0. Switch to the directory in which your source subdirectory is, e.g., trunk/

1. Checkout clean smtinterpol git repository.
   git clone https://github.com/ultimate-pa/smtinterpol.git smtinterpol.git

2. Find out the last merged version by looking into Version.properties
   cat source/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.properties
   The version number looks e.g., like 2.1-228-g5118445

3. Create a patch for the changes from SMTInterpol/src and Library-SMTLIB/src.
   cd smtinterpol.git
   git diff <version-number-last-merged> SMTInterpol/src Library-SMTLIB/src >smtinterpol.diff
   cd ../source
   patch -p1 < ../smtinterpol.git/smtinterpol.diff

4. Update Version.properties.  The easiest way to do this is:
   cd ../smtinterpol.git
   ant
   cd ../source/SMTInterpol/src
   unzip ../../../smtinterpol.git/smtinterpol.jar \*Version.properties
   cd ../../..

5. Make sure you added all new files and deleted all old files.  Run

   diff -x.svn -r source/SMTInterpol/src smtinterpol.git/SMTInterpol/src
   diff -x.svn -r source/Library-SMTLIB/src smtinterpol.git/Library-SMTLIB/src

   it should list some files from ultimate/util, Versions.properties, 
   and the automatically build parser/lexer files and the parser build
   scripts which are slightly different for smtinterpol.

6. Do an git status and check if only changes are in src subdirectory.

7. Check if everything works in Eclipse.

8. Find out the version of the SMTInterpol version that you just merged.
   cat source/SMTInterpol/src/de/uni_freiburg/informatik/ultimate/smtinterpol/Version.properties

9. Commit die updated Ultimate.
   git commit source/SMTInterpol source/Library-SMTLIB
   The log message should say (version can be found by executing "git describe" 
   in smtinterpol.git)

   Updated SMTInterpol to version 2.1-228-g5118445
   from https://github.com/ultimate-pa/smtinterpol.git



Written by Jochen Hoenicke, minor changes done by Matthias Heizmann.
