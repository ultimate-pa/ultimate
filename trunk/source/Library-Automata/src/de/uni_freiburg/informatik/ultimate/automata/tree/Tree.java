package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.List;

public class Tree<LETTER> {

	private TreeNode<LETTER> root;
	private List<TreeNode<LETTER>> leafList;
	
	public Tree(TreeNode<LETTER> root) {
		this.root = root;
		this.leafList = new ArrayList<TreeNode<LETTER>>();
	}
	
	public void addLeaf(TreeNode<LETTER> leaf) {
		this.leafList.add(leaf);
	}
	
	public TreeNode<LETTER> getRoot() {
		return this.root;
	}
	
	public List<TreeNode<LETTER>> getLeafList(){
		return this.leafList;
	}
}
