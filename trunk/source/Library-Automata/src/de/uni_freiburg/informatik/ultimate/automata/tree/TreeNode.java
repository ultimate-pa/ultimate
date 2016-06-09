package de.uni_freiburg.informatik.ultimate.automata.tree;

import java.util.ArrayList;
import java.util.List;

public class TreeNode<LETTER> {

	private final TreeNode<LETTER> parent;
	private final List<TreeNode<LETTER>> children;
	private final LETTER symbol;
	
	public TreeNode(LETTER symbol) {
		this.parent = null;
		this.children = new ArrayList<TreeNode<LETTER>>();
		this.symbol = symbol;
	}
	
	public TreeNode(TreeNode<LETTER> parent, LETTER symbol) {
		this.parent = parent;
		this.children = new ArrayList<TreeNode<LETTER>>();
		this.symbol = symbol;
	}
	
	public void addChild(TreeNode<LETTER> child) {
		children.add(child);
	}
	
	public TreeNode<LETTER> getParent() {
		return this.parent;
	}
	
	public List<TreeNode<LETTER>> getChildren() {
		return this.children;
	}
	
	public LETTER getSymbol() {
		return this.symbol;
	}
	
	public boolean isRoot() {
		if(this.parent.equals(null)) {
			return true;
		} else {
			return false;
		}
	}
	
	public boolean isLeaf() {
		if(this.children.isEmpty()) {
			return true;
		} else {
			return false;
		}
	}
	
	/**
	 * Method to create a Tree. Should be called by root node
	 * @return Returns a Tree.
	 */
	public Tree<LETTER> createTree() {
		final TreeNode<LETTER> treeRoot = this;
		final Tree<LETTER> tree = new Tree<LETTER>(treeRoot);
		if (treeRoot.isLeaf()) {
			tree.addLeaf(treeRoot);	
		} else {
			for(int i = 0; i < treeRoot.getChildren().size() - 1; i++) {
				createTree(treeRoot.getChildren().get(i), tree);
			}
		}
		
		return tree;
	}
	
	private void createTree(TreeNode<LETTER> node, Tree<LETTER> tree) {
		if(node.isLeaf()) {
			tree.addLeaf(node);
		} else {
			for(int i = 0; i < node.getChildren().size() - 1; i++) {
				createTree(node.getChildren().get(i), tree);
			}
		}
	}
}
