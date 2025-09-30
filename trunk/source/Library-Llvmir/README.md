ANTLR Parser Generator for Java
=============================

ANTLR is a Parser Generator for Java.
In this Project, it was used to generate an LLVMIR Parser, including a Listener needed for further building a Boogie AST from the generated LLVMIR ParseTree.

Copyright Notice, License, and Disclaimer
-----------------------------------------

See Antlr_license.txt

Contents
-----------------------------------------

`LLVMIR.g4`: The grammar file for the LLVMIR Parser. As explained avove.

`LlvmirLocation.java`: A simple class to represent a location in an LLVMIR file.

`ParseTreeElementWrapper.java`: A simple wrapper class for ParseTree objects to be used in Ultimate, wrapped as an IElement. It also contains the filename.