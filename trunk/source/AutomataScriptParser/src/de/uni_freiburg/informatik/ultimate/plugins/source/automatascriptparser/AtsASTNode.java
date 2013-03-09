package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;



import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseAST;



/***
 * @author musab@informatik.uni-freiburg.de
 */

public class AtsASTNode extends BaseAST<AtsASTNode> {

	
	/**
	 * 
	 */
	private static final long serialVersionUID = 8077752308820134631L;
	private List<AtsASTNode> children;
	private AtsASTNode parent;
	// The type of the returned value
	protected Class<?> m_returnType;
	// The type the children of this node should have.
	protected Class<?> m_expectingType;

	protected ILocation m_location;
	
	public AtsASTNode() {
		children = new ArrayList<AtsASTNode>();
		parent = null;
		m_location = null;
	}
	
	public AtsASTNode(ILocation loc) {
		super(new Payload(loc, "AtsASTNode"));
		children = new ArrayList<AtsASTNode>();
		parent = null;
		m_location = loc;
	}
	
	public AtsASTNode(AtsASTNode par) {
		children = new ArrayList<AtsASTNode>();
		parent = par;
	}

	
	@Override
	public IPayload getPayload() {
		// TODO Auto-generated method stub
		return new Payload();
	}

	
	public AtsASTNode getIncomingNode() {
		return parent;
	}

	public List<AtsASTNode> getOutgoingNodes() {
		return children;
	}
	
	
	public boolean addIncomingNode(AtsASTNode par) {
		parent = par;
		return true;
	}

	
	public boolean addOutgoingNode(AtsASTNode element) {
		children.add(element);
		if (element != null) {
			((AtsASTNode) element).addIncomingNode(this);
		}
		return true;
	}
	
	public boolean isTypeCorrect(Class<?> expectedType){
		if (m_returnType != null) {
			return m_returnType.isAssignableFrom(expectedType);
		} else {
			return false;
		}
	}
	
	public Class<?> getReturnType() {
		return m_returnType;
	}
	
	public Class<?> getExpectingType() {
		return m_expectingType;
	}

	public void setType(Class<?> type) {
		setReturnType(type);
		setExpectingType(type);
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
	
}
