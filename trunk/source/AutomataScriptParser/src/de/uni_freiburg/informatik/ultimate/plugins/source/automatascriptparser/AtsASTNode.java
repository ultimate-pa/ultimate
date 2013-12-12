package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;



import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseAST;



/***
 * AST Node for AutomataScript parser.
 * @author musab@informatik.uni-freiburg.de
 */

public class AtsASTNode extends BaseAST<AtsASTNode> {

	
	/**
	 * 
	 */
	private static final long serialVersionUID = 8077752308820134631L;
	protected List<AtsASTNode> m_children;
	protected AtsASTNode m_parent;
	// The type of the returned value
	protected Class<?> m_returnType;
	// The type the children of this node should have.
	protected Class<?> m_expectingType;

	protected ILocation m_location;
	private Map<Class<?>, Class<?>> m_primitiveToClassTypes;
	
 	public AtsASTNode() {
		m_children = new ArrayList<AtsASTNode>();
		m_parent = null;
		m_location = null;
		m_primitiveToClassTypes = new HashMap<Class<?>, Class<?>>();
		m_primitiveToClassTypes.put(int.class, Integer.class);
		m_primitiveToClassTypes.put(boolean.class, Boolean.class);
	}
	
	public AtsASTNode(ILocation loc) {
		super(new Payload(loc, "AtsASTNode"));
		m_children = new ArrayList<AtsASTNode>();
		m_parent = null;
		m_location = loc;
	}
	
	public AtsASTNode(AtsASTNode par) {
		m_children = new ArrayList<AtsASTNode>();
		m_parent = par;
	}

	
	@Override
	public IPayload getPayload() {
		// TODO Auto-generated method stub
		return new Payload();
	}

	
	public AtsASTNode getIncomingNode() {
		return m_parent;
	}

	public List<AtsASTNode> getOutgoingNodes() {
		return m_children;
	}
	
	
	public boolean addIncomingNode(AtsASTNode par) {
		m_parent = par;
		return true;
	}

	
	public boolean addOutgoingNode(AtsASTNode element) {
		m_children.add(element);
		if (element != null) {
			((AtsASTNode) element).addIncomingNode(this);
		}
		return true;
	}
	
		
	public Class<?> getReturnType() {
		return m_returnType;
	}
	
	public Class<?> getExpectingType() {
		return m_expectingType;
	}

	public void setType(Class<?> type) {
		Class<?> classType = type;
		if (m_primitiveToClassTypes.containsKey(type)) {
			classType = m_primitiveToClassTypes.get(type);
		}
		setReturnType(classType);
		setExpectingType(classType);
	}
	
	public void setReturnType(Class<?> type) {
		m_returnType = type;
	}
	
	public void setExpectingType(Class<?> type) {
		m_expectingType = type;
	}
	
	
	public ILocation getLocation() {
		return m_location;
	}

	public void setLocation(ILocation loc) {
		mPayload = new Payload(loc, "AtsASTNode");
		m_location = loc;
		
	}
	
	/**
	 * 
	 * @return String representation of this AtsASTNode
	 */
	public String getAsString() {
		StringBuilder builder = new StringBuilder();
		for (AtsASTNode n : m_children) {
			builder.append(n.getAsString());
		}
		return builder.toString();
	}
	
}
