Contents
-----------------------------------------
`LlvmirToBoogieListener.java`: The Listener class that implements the methods to build a Boogie AST from the LLVMIR ParseTree.
This class is outdated and is no longer used in the current implementation of the LLVMIR to Boogie translation.
It remains in the repository for reference purposes only.

`LlvmirToBoogieVisitor.java`: The Visitor class that implements the methods to build a Boogie AST from the LLVMIR ParseTree.
This class is the current implementation used in the LLVMIR to Boogie translation.
It uses the return type Result to provide a bottom-up approach to building the Boogie AST.
It currently reflects the state of extension 13 of the self written LLVMIR Translation guide.

`Result.java`: A simple class to represent the result of visiting a ParseTree node.
It contains lists of Boogie AST nodes, as well as other relevant information needed during the translation process.