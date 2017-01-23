package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

/**
 * Class that represents a Syntax Tree
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 * @param <T>
 */
public class SyntaxTree<T> {
	
	private final SyntaxTreeNode<T> mRootNode;
	
	public SyntaxTree(String rootData) {
		mRootNode = new SyntaxTreeNode(rootData);
	}
	
	public SyntaxTreeNode<T> getRootNode() {
		return mRootNode;
	}
}
