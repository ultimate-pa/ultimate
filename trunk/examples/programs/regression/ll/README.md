# Translation
All files were translated on an **aarch64** Linux system.  
Using the following steps:
1. Run clang -S -emit-llvm -O0 -fno-discard-value-names -UNDEBUG input.c -o output.ll
2. Then remove all instances of "optnone" from the generated .ll file
3. Run opt -S -passes="sroa,mem2reg,simplifycfg" $inputFile -o $outputFile
 
Many translated files also contain string variables. These are currently not translatable and need to be removed.
All implemented features work correctly without these variables.

# Test Folders
#### relevant(_opt)_ll
These folders contain the files that test all currently implemented features.
All but eight tests should be successful.
The tests that fail:
- array10_pattern_simplified(_opt): Uses a library function that is not yet supported.
- IntegerCharacterConstantsRepresentationForSignedChar(_opt): Fails because it was translated on an aarch64 Linux system, where char is treated as unsigned char.
- 6 builtin_(...)overflow(_opt): Fail because they use structType, which has not been implemented yet.
 
#### not_yet_relevant_ll
This folder contains optimized and unoptimized versions of all files that depend on features not yet implemented.
The respective tests should be pass (and moved to the corresponding folder) once the relevant features are implemented.

#### bitOp(_opt)
These folders contain files that use bitwise operations. These operations are currently over-approximated and yield a result of `UNKNOWN`.
All tests in this category pass.

#### self_written
These folders contain hand-written test files designed to test simplified versions of specific features.
All tests in this category should be successful.

# Ranking
The ranking file is a table that shows:
- Which tests should pass and which should fail.
- Which files are expected to work after each planned extension.