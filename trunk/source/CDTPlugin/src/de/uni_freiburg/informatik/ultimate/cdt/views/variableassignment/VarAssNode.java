/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.variableassignment;

import java.util.List;

/**
 * Nodes that we use inside the VariableAssignmentContentProvider
 * 
 * @author Stefan Wissert
 *
 */
public class VarAssNode {
	
	private String name;
	private String value;
	private List<VarAssNode> children;
	private VarAssNode parent;
	
	/**
	 * @param name
	 * @param value
	 */
	public VarAssNode(String name, String value) {
		this.name = name;
		this.value = value;
	}

	/**
	 * @return the children
	 */
	public List<VarAssNode> getChildren() {
		return children;
	}

	/**
	 * @param children the children to set
	 */
	public void setChildren(List<VarAssNode> children) {
		this.children = children;
	}

	/**
	 * @return the parent
	 */
	public VarAssNode getParent() {
		return parent;
	}

	/**
	 * @param parent the parent to set
	 */
	public void setParent(VarAssNode parent) {
		this.parent = parent;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return the value
	 */
	public String getValue() {
		return value;
	}
	
}
