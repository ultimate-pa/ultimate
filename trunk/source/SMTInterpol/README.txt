SMTInterpol in Ultimate
=======================

SMTInterpol is merged manually into Ultimate.  Here are the
necessary steps.

1. Checkout clean smtinterpol git repository.
   cd ...ultimate/source
   git clone https://github.com/juergenchrist/smtinterpol smtinterpol.git

2. Copy SMTInterpol/src and LibrarySMTLIB/src over the existing directories.
   rsync -va --exclude=.svn --delete smtinterpol.git/LibrarySMTLIB/src LibrarySMTLIB
   rsync -va --exclude=.svn --delete smtinterpol.git/SMTInterpol/src SMTInterpol

3. Move the following files from LibrarySMTLIB to LibraryUltimate:
    src/de/uni_freiburg/informatik/ultimate/util/HashUtils.java
    src/de/uni_freiburg/informatik/ultimate/util/ScopedArrayList.java
    src/de/uni_freiburg/informatik/ultimate/util/ScopedHashMap.java
    src/de/uni_freiburg/informatik/ultimate/util/ScopedHashSet.java
    src/de/uni_freiburg/informatik/ultimate/util/ScopeUtils.java
    src/de/uni_freiburg/informatik/ultimate/util/UnifyHash.java

4. Make sure to remove outdated files from svn and add new files to svn.

5. Update Version.properties.  The easiest way to do this is:
   cd smtinterpol.git
   ant
   cd ../SMTInterpol/src
   unzip ../../smtinterpol.git/smtinterpol.jar \*Versions.properties

6. Make sure you added all new files and deleted all old files.  Run

   diff -x.svn -r SMTInterpol/src smtinterpol.git/SMTInterpol/src
   diff -x.svn -r LibrarySMTLIB/src smtinterpol.git/LibrarySMTLIB/src

   it should list the moved files from ultimate/util, Versions.properties, 
   and maybe the automatically build parser/lexer files.

7. Do an svn status and check if only changes are in src subdirectory.
8. Check if everything works in Eclipse.
9. svn commit.  The log message should say (version can be found by 
   executing "git describe" in smtinterpol.git)

   Updated SMTInterpol to version 2.1-102-g04e1b50
   from https://github.com/juergenchrist/smtinterpol
