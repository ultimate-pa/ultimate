package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.List;

/**
 * Class to create a tree for the tree automaton.
 * @author grugelt@uni-freiburg.de
 */
public class Tree<LETTER> {

	/*
	 * Variables
	 */
	private TreeNode<LETTER> mRoot;
	private List<TreeNode<LETTER>> mLeafList;
	
	public Tree(TreeNode<LETTER> root) {
		this.mRoot = root;
		this.mLeafList = new ArrayList<TreeNode<LETTER>>();
	}
	
	public void addLeaf(TreeNode<LETTER> leaf) {
		this.mLeafList.add(leaf);
	}
	
	public TreeNode<LETTER> getRoot() {
		return this.mRoot;
	}
	
	public List<TreeNode<LETTER>> getLeafList(){
		return this.mLeafList;
	}
}
