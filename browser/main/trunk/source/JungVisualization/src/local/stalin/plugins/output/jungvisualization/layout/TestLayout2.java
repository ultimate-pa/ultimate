package local.stalin.plugins.output.jungvisualization.layout;

import java.awt.Font;
import java.awt.font.FontRenderContext;
import java.awt.geom.Rectangle2D;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import local.stalin.model.Edge;
import local.stalin.model.IEdge;
import local.stalin.model.INode;
import local.stalin.model.Payload;
import local.stalin.plugins.output.jungvisualization.graph.GraphProperties;
import edu.uci.ics.jung.algorithms.layout.AbstractLayout;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.graph.util.EdgeType;
import edu.uci.ics.jung.visualization.VisualizationViewer;

public class TestLayout2 extends AbstractLayout<INode, IEdge> {
	
	private ArrayList<IEdge> backEdges;
	private INode rootNode;
	private HashMap<String,INode> nodes = new HashMap<String, INode>();
	private HashMap<String,NodeInfo> nodeInfos = new HashMap<String, NodeInfo>();
	//Graph<INode, IEdge> graph;

	protected TestLayout2(Graph<INode, IEdge> graph) {
		super(graph);
		// TODO Auto-generated constructor stub
	}
	
	public TestLayout2(Graph<INode, IEdge> graph, INode root) {
		super(graph);
		// TODO Auto-generated constructor stub
		//this.graph = graph;
		this.rootNode = root;
	}
	
	@Override
	public void initialize() {
		//0. initilalize help data structures
		storeNodes();
		System.out.println("    STEP  0   ");
		
		//1. make graph acyclic - remove back edges
		CycleDetector cd = new CycleDetector(graph);
		cd.removeCycles(rootNode);
		System.out.println("    STEP  1   ");
		
		//2. assign vertices to layers, add dummy vertices
		LayeringManager lm = new LayeringManager();
		HashMap<INode,Integer> nodeLayers = lm.getLayers(graph, rootNode);
		this.storeNodeInfos(nodeLayers);
		this.insertDummyNodes();
		System.out.println("    STEP  2   ");
		
		//3. order vertices within layers - crossing reduction
		OrderingManager om = new OrderingManager(nodes, nodeInfos, nodeLayers);
		HashMap<Integer, ArrayList<NodeInfo>> nodeOrder = om.getNodeOrder();
		System.out.println("    STEP  3   ");
		
		//4. compute coordinates for vertices
		CoordinatesManager cm = new CoordinatesManager(nodes, nodeInfos, nodeOrder);
		cm.setX();
		cm.setY();
		
		Iterator<String> it = nodeInfos.keySet().iterator();
		while (it.hasNext()){
			String id = it.next();
			//System.out.println(nodes.get(id).getPayload().getName() + " X " + nodeInfos.get(id).getXcoordinate() + " Y "  +  nodeInfos.get(id).getYcoordinate());
			setLocation(nodes.get(id), nodeInfos.get(id).getXcoordinate(), nodeInfos.get(id).getYcoordinate());		
		}
		System.out.println("    STEP  4   ");
		
		//5. add back edges
		if (!cd.getBackEdges().isEmpty()){
			for (IEdge backedge : cd.getBackEdges()){
//				graph.addEdge(backedge, backedge.getSource(), backedge.getTarget(), EdgeType.DIRECTED);
			}
		}
		System.out.println("    STEP  5   ");
	}

	@Override
	public void reset() {
		// TODO Auto-generated method stub
		
	}
	
	private void storeNodes(){
		
		Collection<INode> vertices = getGraph().getVertices();
		
		for (INode n : vertices){
			
			nodes.put(n.getPayload().getID().toString(), n);
		}
	}
	
	private void storeNodeInfos(HashMap<INode,Integer> nodeLayers){
		
		String id;
		
		VisualizationViewer<INode, IEdge> vv = GraphProperties.getInstance().getVVforLayout();
		final Font font = vv.getFont();
		final FontRenderContext frc = vv.getFontMetrics(font).getFontRenderContext();
		
		Rectangle2D bounds;
		
		Iterator<INode> iter = nodeLayers.keySet().iterator();
		
		while (iter.hasNext()){
			NodeInfo ninfo = new NodeInfo();
			INode inode = iter.next();
			id =  inode.getPayload().getID().toString();
			bounds = font.getStringBounds(inode.toString(), frc);
			
			ninfo.setWidth((float)bounds.getWidth() + 2);
			ninfo.setLayer(nodeLayers.get(inode).intValue());
			ninfo.setStalinID(id);
			nodeInfos.put(id, ninfo);
		}
	}
	
	
	public void insertDummyNodes(){
		
		int dummyCounter = 1;
		Iterator<String> it = nodeInfos.keySet().iterator();
		
//		HashMap<String, INode> dummyNodes = new HashMap<String, INode>();
		HashMap<String, NodeInfo> dummyInfos = new HashMap<String, NodeInfo>();
		while (it.hasNext()){
			String id = it.next();
			
			NodeInfo sNodeInfo = nodeInfos.get(id);
			INode snode = nodes.get(id);
			
			for (INode tnode : snode.getOutgoingNodes()){
				
				if (nodeInfos.get(tnode.getPayload().getID().toString()).getLayer() - sNodeInfo.getLayer() > 1){
					
					graph.removeEdge(graph.findEdge(snode, tnode));
					
					DummyNode dnode = new DummyNode();
					dnode.addIncomingNode(snode);
					dnode.addOutgoingNode(tnode);
					//Payload payload = new Payload();
					//payload.setName("");
					//dnode.setPayload(payload);
					//String dummy_id = "d" + dummyCounter;

					Edge inEdge = new Edge(snode, dnode);
					Edge outEdge = new Edge(dnode, tnode);
 					dnode.addIncomingEdge(inEdge);
					dnode.addOutgoingEdge(outEdge);					
					
					NodeInfo ninfo = new NodeInfo();
					ninfo.setStalinID(dnode.getPayload().getID().toString());
					ninfo.setLayer(sNodeInfo.getLayer()+1);
					ninfo.setWidth(0);
					ninfo.setDummy(true);
					
//					dummyNodes.put(dummy_id, dnode);
					//dummyInfos.put(dummy_id, ninfo);
					
//					nodeInfos.put(dummy_id, ninfo);
					
					//System.out.println(dnode.getPayload().getID());
					
					graph.addVertex(dnode);
					graph.addEdge(inEdge, inEdge.getSource(), inEdge.getTarget());
					graph.addEdge(outEdge, outEdge.getSource(), outEdge.getTarget());
					
					nodes.put(ninfo.getStalinID(), dnode);
					dummyCounter ++;
					
				}
			}
			
			
			
			//System.out.println(nodes.get(id).getPayload().getName() + " X " + nodeInfos.get(id).getXcoordinate() + " Y "  +  nodeInfos.get(id).getYcoordinate());
			//setLocation(nodes.get(id), nodeInfos.get(id).getXcoordinate(), nodeInfos.get(id).getYcoordinate());		
		}
		
		it = dummyInfos.keySet().iterator();
		
		while (it.hasNext()) {
			String id = it.next();
			
			NodeInfo ninfo = dummyInfos.get(id);
			nodeInfos.put(id, ninfo);
		}
	}
	

	public void setBackEdges(ArrayList<IEdge> backEdges) {
		this.backEdges = backEdges;
	}

	public ArrayList<IEdge> getBackEdges() {
		return backEdges;
	}

	public void setRootNode(INode rootNode) {
		this.rootNode = rootNode;
	}

	public INode getRootNode() {
		return rootNode;
	}

}
