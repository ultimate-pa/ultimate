package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.List;

/**
 * Class that repesents the node of a Syntax Tree.
 * 
 * @author Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 *
 * @param <T>
 */
public class SyntaxTreeNode<T> {
	private T mData = null;
	private List<SyntaxTreeNode> mChildren = new ArrayList<>();
	private SyntaxTreeNode<T> mParent = null;
	
	public SyntaxTreeNode(T data) {
		this.mData = data;
	}
	
	public void addChild(SyntaxTreeNode<T> child) {
		child.setParent(this);
		this.mChildren.add(child);
	}
	
	public void addChild(T data) {
		SyntaxTreeNode<T> newChild = new SyntaxTreeNode<>(data);
		newChild.setParent(this);
		mChildren.add(newChild);
	}
	
	public void addChildren(List<SyntaxTreeNode> children) {
		for (SyntaxTreeNode<T> t : children) {
			t.setParent(this);
		}
		this.mChildren.addAll(children);
	}
	
	public void removeChild(SyntaxTreeNode<T> child) {
		this.mChildren.remove(child);
	}
	
	public List<SyntaxTreeNode> getChildren() {
		return mChildren;
	}
	
	public T getData() {
		return mData;
	}
	
	public void setData(T data) {
		this.mData = data;
	}
	
	private void setParent(SyntaxTreeNode<T> parent) {
		this.mParent = parent;
	}
	
	public SyntaxTreeNode<T> getParent() {
		return mParent;
	}
	
	public boolean isRoot() {
		return mParent == null;
	}
	
	@Override
	public String toString() {
		String indent = "****";
		String res = "";
		res += "NODE: " + mData + "\n";
		res += "CHILDREN: \n ";
		res += childrenToString(indent);
		return res;
	}
	
	public String childrenToString(String indent) {
		String ind = "****" + indent;
		String res = "";
		for (SyntaxTreeNode<T> child : mChildren) {
			res += ind + "**" + child.getData() + "\n";
			res += ind + "***children of " + child.getData() + ": \n " + child.childrenToString(ind) + "\n";
		}
		return res;
	}
}
