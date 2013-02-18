import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.IPayload;
import local.stalin.plugins.generator.lazyabstraction.UnwindingNode;

/**
 * 
 */

/**
 * @author alexander
 *
 */
public class CoveringEdge implements IEdge {

	/**
	 * 
	 */
	private static final long serialVersionUID = 5078638810029268884L;

	UnwindingNode m_source;
	UnwindingNode m_target;

	public CoveringEdge(UnwindingNode source, UnwindingNode target) {
		m_source = source;
		m_target = target;
	}
	
	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#getSource()
	 */
	@Override
	public INode getSource() {
		return m_source;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#getTarget()
	 */
	@Override
	public INode getTarget() {
		return m_target;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#setSource(local.stalin.model.INode)
	 */
	@Override
	public void setSource(INode source) {
		m_source = (UnwindingNode) source;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IEdge#setTarget(local.stalin.model.INode)
	 */
	@Override
	public void setTarget(INode target) {
		m_target = (UnwindingNode) target;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#getPayload()
	 */
	@Override
	public IPayload getPayload() {
		return null;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#hasPayload()
	 */
	@Override
	public boolean hasPayload() {
		return false;
	}

	/* (non-Javadoc)
	 * @see local.stalin.model.IElement#setPayload(local.stalin.model.IPayload)
	 */
	@Override
	public void setPayload(IPayload payload) {
		
	}

}
