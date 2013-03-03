package de.uni_freiburg.informatik.ultimate.plugins.generator.reimpact;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.StripAnnotationsTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class RIGraphWriter {

	HashSet<IEdge> visited;
	//	int index = 0;
	boolean m_annotateEdges = true;
	boolean m_annotateNodes = true;
	boolean m_rankByLocation = false;
	//	boolean clusterWithCopy = false;

	StringBuilder graph;
	HashMap<String, ArrayList<String>> locToLabel;
	Script m_script;
	private StripAnnotationsTermTransformer m_stripAnnotationsTT = new StripAnnotationsTermTransformer();
	private static Logger s_logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	private HashMap<UnwindingNode, UnwindingNode> m_coveringRelation = new HashMap<UnwindingNode, UnwindingNode>();
	
	String imagePath;

	boolean m_dontWrite = false;

	/*
	 * Initialize the Graphwriter with some options
	 * @param annotateEdges annotate the edges?
	 * @param annotateNodes
	 * @param showUnreachableEdges
	 * @param rankByLocation
	 */
	public RIGraphWriter(String imagePath, boolean annotateEdges, 
			boolean annotateNodes, boolean showUnreachableEdges, 
			boolean rankByLocation, Script script) {
		this.imagePath = imagePath;
		if(imagePath.equals(""))
			m_dontWrite = true;
		this.m_annotateEdges = annotateEdges;
		this.m_annotateNodes = annotateNodes;
		this.m_rankByLocation = rankByLocation;
		m_script = script;
	}


//	public void writeGraphAsImage(UnwindingNode root, String fileName) {
//		if(m_dontWrite)
//			return;
//		else {
//			GraphViz gv = new GraphViz();
//
//			locToLabel = new HashMap<String, ArrayList<String>>();
//
//			gv.addln(gv.start_graph());
//
//			HashSet<UnwindingNode> allNodes = collectNodes(root);
//			ArrayList<GraphEdge> allEdges = collectEdges(allNodes);
//
//			gv.addln(writeNodesToString(allNodes).toString());
//			gv.addln(writeEdgesToString(allEdges).toString());
//
//			gv.addln(gv.end_graph());
//
//			//		}
//
//			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
//					new File(imagePath + "/" + fileName + ".png"));
//			//		index++;
//		}
//	}

	public void writeGraphAsImage(UnwindingNode root, String fileName, TreeSet<UnwindingNode> openNodes) {
		if(!m_dontWrite) {
			s_logger.debug("outputting png: " + fileName);
			
			GraphViz gv = new GraphViz();
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<UnwindingNode> allNodes = collectNodes(root);
			ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeString(allNodes, allEdges, openNodes));

			gv.addln(gv.end_graph());

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
		}
	}

	HashSet<UnwindingNode> collectNodes(UnwindingNode root) {
		ArrayList<UnwindingNode> openNodes = new ArrayList<UnwindingNode>();
		HashSet<UnwindingNode> allNodes = new HashSet<UnwindingNode>(); 
		boolean hasChanged = true;

		openNodes.add(root);
		allNodes.add(root);

		while(hasChanged) {
			hasChanged = false;

			ArrayList<UnwindingNode> current_openNodes = (ArrayList<UnwindingNode>) openNodes.clone();

			for(UnwindingNode node : current_openNodes) {
				ArrayList<RIAnnotatedProgramPoint> outNodes = node.getOutgoingNodes() == null ? 
						new ArrayList<RIAnnotatedProgramPoint>() : 
							new ArrayList<RIAnnotatedProgramPoint>(node.getOutgoingNodes());

				for(RIAnnotatedProgramPoint n : outNodes) {
					if(!allNodes.contains(n)) {
						allNodes.add((UnwindingNode) n);
						openNodes.add((UnwindingNode) n);
						hasChanged = true;
					}
				}
				openNodes.remove(node);
			}
		}
		return allNodes;
	}

	ArrayList<GraphEdge> collectEdges(HashSet<UnwindingNode> allNodes) {
		ArrayList<GraphEdge> allEdges = new ArrayList<GraphEdge>();

		for(Iterator<UnwindingNode> it = allNodes.iterator(); it.hasNext();){
			UnwindingNode node = it.next();
			for(RIAnnotatedProgramPoint outNode : node.getOutgoingNodes()) {
				allEdges.add(new GraphEdge(node,
						((UnwindingNode) node).getOutgoingEdgeLabel((RIAnnotatedProgramPoint) outNode),
						(UnwindingNode) outNode));
			}
		}
		return allEdges;
	}

	StringBuilder writeNodesToString(HashSet<UnwindingNode> allNodes) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<UnwindingNode> it = allNodes.iterator(); it.hasNext();){
			if(m_annotateNodes) {
				graph.append(getLabeledNode((UnwindingNode) it.next()) + "\n");
			}
			else {
				graph.append(convertNodeName(it.next()) + "\n");
			}
		}
		return graph;
	}

	StringBuilder writeEdgesToString(ArrayList<GraphEdge> allEdges) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();){
			graph.append(convertEdgeName(it.next()) + "\n");
		}

		return graph;
	}
	
	StringBuilder writeCoveringEdgesToString() {
		StringBuilder sb = new StringBuilder();
		for ( Entry<UnwindingNode, UnwindingNode>  entry : m_coveringRelation.entrySet()) {
			StringBuilder edgeName = new StringBuilder();
			edgeName.append(convertNodeName(entry.getKey())
					+ " -> " + convertNodeName(entry.getValue()));
			edgeName.append("[weight=0, color=red, style=dashed] ;");
				
			sb.append(edgeName.toString());
		}
		return sb;
	}


	String writeString(HashSet<UnwindingNode> allNodes, ArrayList<GraphEdge> allEdges, TreeSet<UnwindingNode> openNodes) {
		StringBuilder graph = new StringBuilder(); 

		graph.append(this.writeNodesToString(allNodes));
		graph.append(this.writeEdgesToString(allEdges));

//		graph.append(this.writeCoveringEdgesToString()); //weight = 0 does not work well enough, so this affects the layout..
		
		for(UnwindingNode n : openNodes) {
			graph.append(
					(m_annotateNodes ? 
							getLabeledNode(n,  "color=grey, style=filled") : 
								convertNodeName(n) + " [color=grey, style=filled] ; "));
		}

		return graph.toString();
	}

	String convertNodeName(UnwindingNode node) {
		String name = node.toString();

		String quotName = "\"" + name + "\"";

		return quotName;
	}

	private String getLabeledNode(UnwindingNode node){
		return getLabeledNode(node, "");
	}

	private String getLabeledNode(UnwindingNode node, String additionalOptions) {
		String quotName = convertNodeName(node);
		String name = quotName.replace("\"", "");
		String nodeLabel;

		Term assertion;
		try {
			assertion = node.getPredicate().getFormula();
		} catch (UnsupportedOperationException e) {
			assertion = m_script.term("true");
		}
				 

		FormulaUnLet unLet = new FormulaUnLet();
		assertion = unLet.unlet(assertion);

		String coveredBy = "";
		if (node.isCovered()&& node.m_coveringNode != null) {
			coveredBy = convertNodeName(node.m_coveringNode);
			coveredBy = coveredBy.substring(1, coveredBy.length()-1);
			coveredBy = "\\n covBy: " + coveredBy;
			m_coveringRelation.put(node, node.m_coveringNode);
		}
		
		String pcImportant = node.isPreCallNodeImportant ? "\\n pcnImportant" : "";
		
		nodeLabel = "\n" + quotName 
				+ "[label = \"" + name + "\\n" 
				+ prettifyFormula(assertion) + coveredBy 
				+ pcImportant
				//+ "\\n" + node.m_preorderIndex 
				+ "\"" + (additionalOptions == "" ? "" : ", " + additionalOptions) 
				+ "];" + "\n";
			
		return nodeLabel;
	}

	boolean m_edgesWithHash = false;

	String convertEdgeName(GraphEdge edge) {
		StringBuilder edgeName = new StringBuilder();
		edgeName.append(convertNodeName(edge.source)
				+ " -> " + convertNodeName(edge.target));

		if(m_annotateEdges){
			String edgeLabel; 
			if (edge.code instanceof Call)
				edgeLabel = "Call";
			else if (edge.code instanceof Return)
				edgeLabel = "Return";
			else 
				edgeLabel = edge.code.getPrettyPrintedStatements();
					
			edgeName.append("[label=\""+ edgeLabel + "\"]");
		}
		return edgeName.toString();
	}

	String prettifyFormula(Term f) {
		//		StringBuilder sb = new StringBuilder(f.toString());
		boolean prettify = false;
		if (prettify) {
//			String toReturn = f.toString().replaceAll("(_b[0-9]*)|(_[0-9]*)", "");
			String toReturn = m_stripAnnotationsTT.transform(f).toString();
			return toReturn;
		}
		else
			return f.toString();
	}
	
	class GraphEdge {
		UnwindingNode source;
		UnwindingNode target;
		CodeBlock code;
		
		public GraphEdge(UnwindingNode source, CodeBlock code, UnwindingNode target) {
			this.source = source;
			this.code = code;
			this.target = target;
		}
		
		public String toString() {
			return source.toString() + 
					" --" + code.toString() +
					"--> " + target.toString();
		}
	}
}
