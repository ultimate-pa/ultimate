package local.stalin.plugins.generator.rcfgbuilder;

import local.stalin.core.api.StalinServices;
import local.stalin.model.AbstractEdgeNode;
import local.stalin.model.AbstractElement;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.Payload;

import org.apache.log4j.Logger;

public abstract class TransEdge extends AbstractElement implements IEdge {

	private static final long serialVersionUID = 6825950584198385523L;

	static Logger s_Logger = 
		StalinServices.getInstance().getLogger(Activator.PLUGIN_ID);

	private AbstractEdgeNode m_source;
	private AbstractEdgeNode m_target;
	
	public TransEdge() {
		super.setPayload(new Payload());
	}
	
	
	public void connectSource(LocNode source) {
		if (source !=null) {
			m_source = source;
			source.addOutgoingEdge(this);
			s_Logger.debug("Edge " + this + " is successor of Node " + source);
		}
	}
	
	public void connectTarget(LocNode target) {
		if (target != null) {
			m_target = target;
			target.addIncomingEdge(this);
			s_Logger.debug("Node " + target + " is successor of Edge " + this);
		}
	}


	@Override
	public INode getSource() {
		return m_source;
	}

	@Override
	public INode getTarget() {
		return m_target;
	}

	@Override
	public void setSource(INode source) {
		m_source = (AbstractEdgeNode) source;

	}

	@Override
	public void setTarget(INode target) {
		m_target = (AbstractEdgeNode) target;

	}

	public String toString() {
		return this.getPayload().getName();
	}
	
	


}
