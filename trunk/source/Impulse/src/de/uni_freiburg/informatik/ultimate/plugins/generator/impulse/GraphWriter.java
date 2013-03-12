package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet.UnletType;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.StripAnnotationsTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class GraphWriter {

	HashSet<IEdge> visited;
	//	int index = 0;
	boolean m_annotateEdges = true;
	boolean m_annotateNodes = true;
	boolean m_showUnreachableEdges = true;
	boolean m_rankByLocation = false;
	boolean m_showNodeToCopy = true;
	
	boolean m_hideUnreachableOnce = false;
	//	boolean clusterWithCopy = false;

	StringBuilder graph;
	HashMap<String, ArrayList<String>> locToLabel;
	Script m_script;
	StripAnnotationsTermTransformer m_satt;

	String imagePath;

	boolean m_dontWrite = false;

	/*
	 * Initialize the Graphwriter with some options
	 * @param annotateEdges annotate the edges?
	 * @param annotateNodes
	 * @param showUnreachableEdges
	 * @param rankByLocation
	 */
	public GraphWriter(String imagePath, boolean annotateEdges, 
			boolean annotateNodes, boolean showUnreachableEdges, boolean rankByLocation, Script script) {
		this.imagePath = imagePath;
		if(imagePath == "")
			m_dontWrite = true;
		this.m_annotateEdges = annotateEdges;
		this.m_annotateNodes = annotateNodes;
		this.m_showUnreachableEdges = showUnreachableEdges;
		this.m_rankByLocation = rankByLocation;
		m_script = script;
		m_satt = new StripAnnotationsTermTransformer();
	}


	public void writeGraphAsImage(AnnotatedProgramPoint root, String fileName) {
		if(m_dontWrite)
			return;
		else {
			GraphViz gv = new GraphViz();
			//		visited = new HashSet<IEdge>();
			//		graph = new StringBuilder();	
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<AnnotatedProgramPoint> allNodes = collectNodes(root);
			ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeNodesToString(allNodes).toString());
			gv.addln(writeEdgesToString(allEdges).toString());

			gv.addln(gv.end_graph());

			//		}

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
			//		index++;
		}
	}


	public void writeGraphAsImage(AnnotatedProgramPoint root, String fileName,
			AnnotatedProgramPoint[] error_trace) {
		
		if(m_dontWrite)
			return;
		else {
			GraphViz gv = new GraphViz();
			//		visited = new HashSet<IEdge>();
			//		graph = new StringBuilder();	
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<AnnotatedProgramPoint> allNodes = collectNodes(root);
			ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeNodesToString(allNodes).toString());
			
			ArrayList<AnnotatedProgramPoint> error_trace_al = new ArrayList<AnnotatedProgramPoint>();
			for (int i = 0; i < error_trace.length; i++)
				error_trace_al.add(error_trace[i]);
			gv.addln(writeEdgesToString(allEdges, error_trace_al).toString());

			gv.addln(gv.end_graph());

			//		}

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
			//		index++;
		}
	}
	
	public void writeGraphAsImage(AnnotatedProgramPoint root, String fileName,
			HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy_current, 
			HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		if(m_dontWrite)
			return;
		else {
			GraphViz gv = new GraphViz();
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<AnnotatedProgramPoint> allNodes = collectNodes(root);
			ArrayList<GraphEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeString(allNodes, allEdges, nodeToCopy_current, nodeToCopy));

			gv.addln(gv.end_graph());

			//		}

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
			//		index++;
		}
	}

//	HashSet<INode> collectNodes(AnnotatedProgramPoint root) {
//		ArrayList<INode> openNodes = new ArrayList<INode>();
//		HashSet<INode> allNodes = new HashSet<INode>(); 
//		boolean hasChanged = true;
//
//		openNodes.add(root);
//
//		while(hasChanged) {
//			hasChanged = false;
//
//			ArrayList<INode> current_openNodes = (ArrayList<INode>) openNodes.clone();
//
//			for(INode node : current_openNodes) {
//				ArrayList<IEdge> edges = new ArrayList<IEdge>(node.getOutgoingEdges());
//				if(m_showUnreachableEdges && !m_hideUnreachableOnce)
//					edges.addAll(node.getIncomingEdges());
//
//				for(IEdge e : edges) {
//					INode nextNode = e.getSource();
//					if(!allNodes.contains(nextNode)) {
//						allNodes.add(nextNode);
//						openNodes.add(nextNode);
//						hasChanged = true;
//					}
//					nextNode = e.getTarget();
//					if(!allNodes.contains(nextNode)) {
//						allNodes.add(nextNode);
//						openNodes.add(nextNode);
//						hasChanged = true;
//					}
//				}
//				openNodes.remove(node);
//			}
//		}
//		return allNodes;
//	}
	
	HashSet<AnnotatedProgramPoint> collectNodes(AnnotatedProgramPoint root) {
		ArrayList<AnnotatedProgramPoint> openNodes = new ArrayList<AnnotatedProgramPoint>();
		HashSet<AnnotatedProgramPoint> allNodes = new HashSet<AnnotatedProgramPoint>(); 
		boolean hasChanged = true;

		openNodes.add(root);
		allNodes.add(root);

		while(hasChanged) {
			hasChanged = false;

			ArrayList<AnnotatedProgramPoint> current_openNodes = (ArrayList<AnnotatedProgramPoint>) openNodes.clone();

			for(AnnotatedProgramPoint node : current_openNodes) {
				ArrayList<AnnotatedProgramPoint> inOutNodes = node.getOutgoingNodes() == null ? 
						new ArrayList<AnnotatedProgramPoint>() : 
							new ArrayList<AnnotatedProgramPoint>(node.getOutgoingNodes());


				if(m_showUnreachableEdges && 
						!m_hideUnreachableOnce && 
						node.getIncomingNodes() != null)
					inOutNodes.addAll(node.getIncomingNodes());


				for (AnnotatedProgramPoint n : inOutNodes) {
					if(!allNodes.contains(n)) {
						allNodes.add((AnnotatedProgramPoint) n);
						openNodes.add((AnnotatedProgramPoint) n);
						hasChanged = true;
					}
				}
				openNodes.remove(node);
			}
		}
		return allNodes;
	}
	
	

	ArrayList<GraphEdge> collectEdges(HashSet<AnnotatedProgramPoint> allNodes) {
		ArrayList<GraphEdge> allEdges = new ArrayList<GraphEdge>();

		for(Iterator<AnnotatedProgramPoint> it = allNodes.iterator(); it.hasNext();){
			AnnotatedProgramPoint node = it.next();
			for(AnnotatedProgramPoint outNode : node.getOutgoingNodes()) {
				allEdges.add(new GraphEdge(node,
						((AnnotatedProgramPoint) node).getOutgoingEdgeLabel((AnnotatedProgramPoint) outNode),
						(AnnotatedProgramPoint) outNode));
			}
		}
		return allEdges;
	}

	StringBuilder writeNodesToString(HashSet<AnnotatedProgramPoint> allNodes) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<AnnotatedProgramPoint> it = allNodes.iterator(); it.hasNext();){
			if(m_annotateNodes) {
				graph.append(getLabeledNode(it.next()) + "\n");
			}
			else {
				graph.append(convertNodeName(it.next()) + "\n");
			}
		}

		return graph;
	}

//	StringBuilder writeEdgesToString(HashSet<IEdge> allEdges) {
//		StringBuilder graph = new StringBuilder(); 
//
//		for(Iterator<IEdge> it = allEdges.iterator(); it.hasNext();){
//			graph.append(convertEdgeName(it.next()) + "\n");
//		}
//
//		return graph;
//	}

	StringBuilder writeEdgesToString(ArrayList<GraphEdge> allEdges) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();){
			graph.append(convertEdgeName(it.next()) + "\n");
		}

		return graph;
	}
	
	private Object writeEdgesToString(ArrayList<GraphEdge> allEdges,
			ArrayList<AnnotatedProgramPoint> error_trace) {
		if(error_trace == null)
			return writeEdgesToString(allEdges);
		
		StringBuilder graph = new StringBuilder(); 

		String label = "";
		
		for(Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();) {
			GraphEdge current = it.next();
			if (error_trace.contains(current.source) && 
					error_trace.contains(current.target) &&
					!current.source.equals(current.target))
				label = "[color=blue]";
			graph.append(convertEdgeName(current) + label + "\n");
			label = "";
		}

		return graph;
	}

	
	StringBuilder writeEdgesToString(ArrayList<GraphEdge> allEdges,
			HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<GraphEdge> it = allEdges.iterator(); it.hasNext();){
			GraphEdge edge = it.next();
			graph.append(convertEdgeName(edge) + 
					(nodeToCopy.values().contains(edge.source) ? " [style=dashed] " : "") 
					+ "\n");
		}

		return graph;
	}

	String writeString(HashSet<AnnotatedProgramPoint> allNodes, ArrayList<GraphEdge> allEdges, 
			HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy_current,
			HashMap<AnnotatedProgramPoint, AnnotatedProgramPoint> nodeToCopy) {
		StringBuilder graph = new StringBuilder(); 

		graph.append(this.writeNodesToString(allNodes));
		graph.append(this.writeEdgesToString(allEdges, nodeToCopy_current));

		for(Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> en : nodeToCopy_current.entrySet()) {
			graph.append(
					//"subgraph \"cluster" + ctr++ + "\" " +
					"{ rank=same; rankdir=LR; " + 
					(m_annotateNodes ? 
							getLabeledNode(en.getKey(),  "color=grey, style=filled") : 
								convertNodeName(en.getKey()) + " [color=grey, style=filled] ; ") + 
					(m_annotateNodes ? 
							getLabeledNode(en.getValue(),  "color=lightblue, style=filled") : 
								convertNodeName(en.getValue()) + " [color=lightblue, style=filled] ;")
					+ "}");
		}
		if(m_showNodeToCopy) {
			for(Entry<AnnotatedProgramPoint, AnnotatedProgramPoint> en : nodeToCopy.entrySet()) {
			graph.append(convertNodeName(en.getKey()) + " -> " + 
				convertNodeName(en.getValue()) + "[weight=0, color=red] ;");
			}
		}
		return graph.toString();
	}

	private String getLabeledNode(AnnotatedProgramPoint node, String additionalOptions) {
		String quotName = convertNodeName(node);
		String name = quotName.replace("\"", "");
		String nodeLabel;
		String assertionString;
		if (node.getPredicate() != null) {
			Term assertion = node.getPredicate().getFormula();

			FormulaUnLet unLet = new FormulaUnLet();
			assertion = unLet.unlet(assertion);
			assertionString = prettifyFormula(assertion) ;
		} else
			assertionString = "noAssertion";

		nodeLabel = "\n" + quotName 
				+ "[label = \"" + name + "\\n" + assertionString
				+ "\" , " + additionalOptions
				+ "];" + "\n";

		return nodeLabel;
	}

	String convertNodeName(AnnotatedProgramPoint node) {
		String name = node.toString();
		//		name = "\"" + name;
		name = name.replace("[", "");
		name = name.replace("ERROR_LOCATION", "EL");
		name = name.replace("ERROR_Pseudo", "PEL");
		name = name.replace(", $Ultimate#", "");
		name = name.replace("$Ultimate#", "");
		name = name.replace("]", "");
//		String sUID = node.getPayload().getID().toString();
		String sUID = (new Integer(node.hashCode())).toString();//.getPayload().getID().toString();
//		name = name + "-" + sUID.substring(0, sUID.length()/8);
		name = name + "-" + sUID.substring(0, sUID.length()/2);
		//		name = name + "\"";

		String quotName = "\"" + name + "\"";

		return quotName;
	}

	private String getLabeledNode(AnnotatedProgramPoint node){
		return getLabeledNode(node, "");
		
//		String quotName = convertNodeName(node);
//		String name = quotName.replace("\"", "");
//		String nodeLabel;
//		SMTNodeAnnotations nodeAnn = 
//				(SMTNodeAnnotations)node.getPayload().getAnnotations().get("SMT");
//		if(nodeAnn != null) {
//			Term assertion = nodeAnn.getAssertion();
//			
//			FormulaUnLet unLet = new FormulaUnLet();
//			assertion = unLet.unlet(assertion);
//			
//			nodeLabel = "\n" + quotName + "[label = \"" + name + "\\n" + prettifyFormula(assertion) + "\"];" + "\n";
//			//				String loc = name.split("-")[0];
//			//				if(locToLabel.get(loc) == null) {
//			//					ArrayList<String> al = new ArrayList<String>();
//			//					al.add(nodeEntry);
//			//					locToLabel.put(loc, al);
//			//				}
//			//				else {
//			//					locToLabel.get(loc).add(nodeEntry);
//			//				}
//		}
//		else {
//			nodeLabel = quotName;
//		}
//		return nodeLabel;
	}

	boolean m_edgesWithHash = false;

	String convertEdgeName(GraphEdge edge) {
		StringBuilder edgeName = new StringBuilder();
		edgeName.append(convertNodeName(edge.source)
				+ " -> " + convertNodeName(edge.target));

		if(m_annotateEdges){
			String edgeLabel;
			if (edge.code == null)
				edgeLabel = "-";
			else if (edge.code instanceof Call)
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
		boolean prettify = true;
		if (prettify) {
//			String toReturn = f.toString().replaceAll("(_b[0-9]*)|(_[0-9]*)", ""); //obsolete since evren's change
//			String toReturn = f.toString().split("location")[0].trim();
			
			Term f1 = m_satt.transform(f);
			String toReturn = f1.toString();
//			String toReturn = f.toString().replaceAll(":location(\\w|\\s|:|/|.|[|])*?\\)", "\\)");
			return toReturn;
		}
		else
			return f.toString();
	}


	public boolean getHideUnreachableOnce() {
		return m_hideUnreachableOnce;
	}


	public void setHideUnreachableOnce(boolean m_hideUnreachableOnce) {
		this.m_hideUnreachableOnce = m_hideUnreachableOnce;
	}
	
	class GraphEdge {
		AnnotatedProgramPoint source;
		AnnotatedProgramPoint target;
		CodeBlock code;
		
		public GraphEdge(AnnotatedProgramPoint source, CodeBlock code, AnnotatedProgramPoint target) {
			this.source = source;
			this.code = code;
			this.target = target;
		}
		
		public String toString() {
			return source.toString() + 
					" --" + (code == null ? "null" : code.toString()) +
					"--> " + target.toString();
		}
	}
}
