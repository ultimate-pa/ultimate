/**
 * 
 */
package local.stalin.model;

import java.io.Serializable;
import java.util.HashSet;

import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;

import org.apache.log4j.Logger;


/**
 * This class is the general model container. It should preselect walkers and
 * perform a number of search operations on its model.
 * 
 * @author dietsch
 * @version 0.0.2
 */
public class ModelContainer implements Serializable{
	

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -1957760572620128974L;

	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	private INode m_GraphRoot;

	private GraphType m_GraphType;

	private String m_GraphName;

	protected ModelContainer(INode rootNode, GraphType type, String name) {
		this.m_GraphRoot = rootNode;
		this.m_GraphType = type;
		this.m_GraphName = name;
		init();
	}

	protected INode findNode(String outerAnnotationKey,
			String innerAnnotationKey, Object innerAnnotationValue) {
		return findNode(outerAnnotationKey, innerAnnotationKey,
				innerAnnotationValue, m_GraphRoot);
	}
	
	protected IPayload findNode(StalinUID id){
		return findNode(id.toString(), this.m_GraphRoot);
	}
	
	protected IPayload findNode(String id){
		return findNode(id, this.m_GraphRoot);
	}
	
	protected static IPayload findNode(String id, INode root) {
		return findNode(id, root, new HashSet<INode>());
	}

	protected static IPayload findNode(String id, INode currentRoot, HashSet<INode> visited) {
		if (visited.contains(currentRoot))
			return null;
		visited.add(currentRoot);
		if (currentRoot.getPayload().getID().equals(id)) {
			return currentRoot.getPayload();
		} else {
			for (IElement n : currentRoot.getOutgoingNodes()) {
				if (n instanceof INode) {
					IPayload rtr_Value = findNode(id, (INode) n, visited);
					if(rtr_Value != null) {
						return rtr_Value;
					}
				}
			}
			return null;
		}
	}

	/**
	 * Finds Nodes based on their annotations. Expects every parameter to be not
	 * null!
	 * Simple recursive depth-first search.
	 * 
	 * @param outerAnnotationKey
	 * @param innerAnnotationKey
	 * @param innerAnnotationValue
	 * @param node
	 * @return Node with given annotation.
	 */
	protected static INode findNode(String outerAnnotationKey,
			String innerAnnotationKey, Object innerAnnotationValue, INode node) {
		// TODO implement search with support for null values (perhaps even
		// nodesets as return values
		if (node.getPayload().getAnnotations().get(outerAnnotationKey).getAnnotationsAsMap().get(
				innerAnnotationKey).equals(innerAnnotationValue)) {
			return node;
		} else {
			INode returnNode = null;
			for (IElement i : node.getOutgoingNodes()) {
				if(i instanceof INode){
					returnNode = findNode(outerAnnotationKey, innerAnnotationKey,
							innerAnnotationValue, (INode)i);					
				}
				if (returnNode != null) {
					return returnNode;
				}
			}
		}
		return null;
	}

	protected INode getRoot() {
		return this.m_GraphRoot;
	}

	protected String getName() {
		return this.m_GraphName;
	}

	protected int getSize() {
		return -1;
	}

	public String toString() {
		return this.m_GraphType.toString();
		//return this.m_GraphName+" ("+m_GraphType.getType()+")";
	}

	protected GraphType getType() {
		return this.m_GraphType;
	}

	private void init() {
		this.m_GraphType.setSize(countNodes(this.m_GraphRoot));
		s_Logger.info(this.m_GraphName + " has "+this.m_GraphType.getSize() +" nodes.");
	}

	protected void cleanup() {
	}
	
	private int countNodes(INode root){
		return 0;
		/*int acc=1;
		for(INode n : root.getOutgoing()){
			acc=acc+countNodes(n);
		}
		return acc;
	*/}

}
