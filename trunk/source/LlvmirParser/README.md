LLVMIR Parser
=============================

This project contains the necessary files to parse LLVM IR files.
The parsed files will be optimized beforehand using the `opt` tool from LLVM.
Hence, the `opt` tool must be installed and available in the system's PATH.

Troubleshooting
-----------------------------------------
If your `opt` installation does not get recognized, you can set the path in the `preferences` of the ultimate GUI.

Contents
-----------------------------------------
`LlvmirOptimizer.java`: A simple class to optimize .ll files using the `opt` tool.

`UltimateLlvmirParser.java`: The main class to parse an LLVMIR file. It uses the generated parser to create a ParseTree and 
parse it as an IElement using the `ParseTreeElementWrapper` from the `Library-Llvmir` project.
- To deactivate the optimization step, set the boolean parameter `optimize` to false.
	In the future this setting should be moved to the preferences of the ultimate GUI.