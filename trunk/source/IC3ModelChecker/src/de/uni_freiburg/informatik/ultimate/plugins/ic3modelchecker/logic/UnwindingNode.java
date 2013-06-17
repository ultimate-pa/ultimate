/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic;

import java.util.ArrayList;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.Activator;

/**
 * @author nutz
 *
 */
public class UnwindingNode extends CFGExplicitNode {
	/**
	 * 
	 */
	private static final long serialVersionUID = -3028451585187599780L;
	
	protected static Logger s_logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private boolean		m_isCovered = false;
	private UnwindingNode m_coveringNode;
	private ArrayList<UnwindingNode> m_coveredNodes = new ArrayList<UnwindingNode>();
	private boolean		m_isLeaf = true; 
	//TODO: wird nicht verwendet -> eventuelle verschoenerung: verwenden und dafuer UnwProcRoot-Klasse aufloesen
	private boolean		m_isRoot = false; 
	protected UnwindingProcRoot m_procRoot;
//	protected Script 		m_script;
	private CFGExplicitNode m_cfgLocation; //der zugehoerige Knoten im CFG - repraesentiert gleichzeitig die Location
//	private List<IEdge> 				m_IncomingEdges		= new ArrayList<IEdge>();
//	private List<IEdge> 				m_OutgoingEdges		= new ArrayList<IEdge>();
	private int m_indexInPreorder;
	private boolean m_isErrorLocation;	

	public UnwindingNode(CFGExplicitNode cfgNode, boolean useSsa, UnwindingProcRoot procRoot) {
		super(cfgNode, useSsa);
		assert (!(cfgNode instanceof UnwindingNode)); // we only copy from the original CFG
		this.m_cfgLocation = cfgNode;
		m_indexInPreorder = 
				//(procRoot != null) ? 
				//procRoot.getPreorder().indexOf(this) : 
					-1; //compute onDemand
		m_procRoot = procRoot;
		m_isErrorLocation = this.getPayload().getName().contains("ERROR");
	}
	
//	public void setAsRoot() {
//		m_isRoot = true;
//	}
//
//	public boolean isRoot() {
//		return m_isRoot;
//	}
	public String toString(){
		return getPayload().getName();
	}

	public void setCovered(boolean m_isCovered) {
		this.m_isCovered = m_isCovered;
	}

	public boolean isCovered() {
		return m_isCovered;
	}

	public void set_coveringNode(UnwindingNode m_coveringNode) {
		this.m_coveringNode = m_coveringNode;
	}

	public UnwindingNode get_coveringNode() {
		return m_coveringNode;
	}

	public ArrayList<UnwindingNode> get_coveredNodes() {
		return m_coveredNodes;
	}

	public void set_isLeaf(boolean m_isLeaf) {
		this.m_isLeaf = m_isLeaf;
	}

	public boolean isLeaf() {
		return m_isLeaf;
	}
	
	public SMTNodeAnnotations getSMTAnnotations(){
		return (SMTNodeAnnotations)this.getPayload().getAnnotations().get("SMT");
	}

	public int getIndexInPreorder() {
		if (m_indexInPreorder == -1) {
			m_indexInPreorder = m_procRoot.getPreorder().indexOf(this);
		}
		return m_indexInPreorder;
	}
	
	public CFGExplicitNode getOriginalCFGNode() {
		return m_cfgLocation;
	}

	public void unwindNode(TreeSet<UnwindingNode> openNodes) {
		for (IEdge iEdge : m_cfgLocation.getOutgoingEdges()) {
			CFGEdge edge = (CFGEdge) iEdge;
			CFGEdge newEdge = edge.copyWithoutNodesUsingSSAMapping(getSMTAnnotations().getSSAMapping());
			newEdge.setSource(this);
			UnwindingNode newNode = new UnwindingNode(
					(CFGExplicitNode) edge.getTarget(), true, m_procRoot);

			newEdge.setTarget(newNode);
			if (!newNode.isErrorLocation())
				this.m_procRoot.addToPreorder(newNode);//!! has to be before add, as otherwise compare fails !!
			openNodes.add(newNode);
		}
	}
	
	
	public boolean isErrorLocation() {
		return m_isErrorLocation;
	}
	
	 
//	public void copyAllSuccessorsFromNode(TreeSet<UnwindingNode> m_openNodes) {
//		this.getSMTAnnotations().m_clonedUsingSSA = true;//useSSA!
//		super.copyAllSuccessorsFromNode(m_cfgLocation);
//		for (IEdge edge : this.m_OutgoingEdges) {
//			UnwindingNode replacement = new UnwindingNode(
//					(CFGExplicitNode) edge.getTarget(), false, this.m_procRoot);
//			edge.setTarget(replacement);
//			m_openNodes.add((UnwindingNode) edge.getTarget());
//			this.m_procRoot.addToPreorder(replacement);
//		}
//	}
}
