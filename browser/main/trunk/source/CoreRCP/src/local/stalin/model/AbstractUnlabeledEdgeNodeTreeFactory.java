package local.stalin.model;

import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;


/**
 * AbstractUnlabeledEdgeNodeTreeFactory
 * @deprecated within STALIN 2.0 should be rewritten using the advantages
 * of the various subclasses of {@link AbstractElement}
 *
 */
@Deprecated
public abstract class AbstractUnlabeledEdgeNodeTreeFactory{ // implements Serializable{
	
	private static class Node extends AbstractNoEdgeNode
	{
		private static final long serialVersionUID = 4113157505082247610L;
		private IPayload m_Payload;
//		private Flags m_Flags;
		private ArrayList<INode> m_Outgoing = new ArrayList<INode>(); 
		
		public Node(final IPayload payload)
		{
			m_Payload = payload;
		}
		
		//@Override
		public IPayload getPayload() {
			if(this.m_Payload == null){
				this.m_Payload = new Payload();
			}
			return this.m_Payload;
		}
	
//		//@Override
//		public Flags getFlags() {
//			if(this.m_Flags == null){
//				this.m_Flags = new Flags();
//			}
//			return m_Flags;
//		}
	
//		//@Override
//		public void setDepth(int depth) {
//			this.getPayload().setDepth(depth);
//			this.updateChildDepth(depth);
//		}
	
		//@Override
		public boolean removeOutgoingNode(INode element) {
			boolean rtr = false;
			if (this.getOutgoingNodes().contains(element)) {
				ListIterator<INode> iter = element.getOutgoingNodes()
						.listIterator();
				int i = this.getOutgoingNodes().indexOf(element);
				this.getOutgoingNodes().remove(i);
				rtr = true;
				while (iter.hasNext()) {
					INode n = iter.next();
					this.getOutgoingNodes().add(i, n);
//					this.updateChildCount(this.getChildCount()+1);
					//n.setDepth(this.getDepth()+1);
					++i;
				}
			}
			return rtr;
		}
	
		//@Override
		public boolean removeIncomingNode(INode element) {
			return false;
		}
	
		//@Override
		public List<INode> getOutgoingNodes() {
			return this.m_Outgoing;
		}
	
		//@Override
		public List<INode> getIncomingNodes() {
			return null;
		}
	
		//@Override
		public void removeAllOutgoing() {
			for(INode n : this.getOutgoingNodes()){
				this.removeOutgoingNode(n);
			}
		}
	
		//@Override
		public void removeAllIncoming() {
	
		}
		//@Override
		public boolean addIncomingNode(INode element) {
			return false;
		}			
		//@Override
		public boolean addOutgoingNode(INode element) {
			boolean rtr = this.m_Outgoing.add(element);
//			if(rtr){
//				element.setDepth(this.getDepth()+1);
//				this.updateChildCount(this.getChildCount()+1);
//			}
			return rtr;
		}
//
//		private void updateChildDepth(int parentDepth){
//			int newDepth = parentDepth+1;
//			for (INode n : this.getOutgoingNodes()){
//				if (n.getPayload().getDepth() != newDepth) {
//					n.setDepth(newDepth);
//				}
//			}
//		}
//		private void updateChildCount(int count){
//			this.getPayload().setChildCount(count);
//		}
//		private int getDepth(){
//			return this.getPayload().getDepth();
//		}
//		private int getChildCount(){
//			return this.getPayload().getChildCount();
//		}

		//@Override
		public void setPayload(IPayload payload) {
			this.m_Payload = payload;
		}

		//@Override
		public boolean hasPayload() {
			return (this.m_Payload != null);
		}
	
	}
	
	private static class Factory extends AbstractUnlabeledEdgeNodeTreeFactory
	{
	/**
	 * 
	 */
	private static final long serialVersionUID = -5428381991359019302L;
	
	public Factory()
	{}
	
	//@Override
	public boolean removeSubtree(INode rootNode, INode subtree) {
		if (rootNode == subtree) {
			return false;
		}
		if (rootNode.getOutgoingNodes().contains(subtree)) {
			return rootNode.getOutgoingNodes().remove(subtree);
		} else {
			for (INode n : rootNode.getOutgoingNodes()) {
				if(removeSubtree(n, subtree)){
					return true;
				}
			}
		}
		return false;
	}
	//@Override
	public INode createNode() {
		return createNode(null);
	}
	//@Override
	public INode createNode(final IPayload payload) {
		return new Node(payload); 

}}
	
	public static AbstractUnlabeledEdgeNodeTreeFactory getFactory(){
		return new Factory();
		}
	
	public abstract INode createNode();
	
	public abstract INode createNode(IPayload payload);
	
	public abstract boolean removeSubtree(INode root, INode subtree);

}
