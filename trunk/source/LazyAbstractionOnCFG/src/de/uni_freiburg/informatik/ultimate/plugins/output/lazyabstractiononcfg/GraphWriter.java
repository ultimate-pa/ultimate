package de.uni_freiburg.informatik.ultimate.plugins.output.lazyabstractiononcfg;

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


	public void writeGraphAsImage(INode root, String fileName) {
		if(m_dontWrite)
			return;
		else {
			GraphViz gv = new GraphViz();
			//		visited = new HashSet<IEdge>();
			//		graph = new StringBuilder();	
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<INode> allNodes = collectNodes(root);
			HashSet<IEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeNodesToString(allNodes).toString());
			gv.addln(writeEdgesToString(allEdges).toString());

			gv.addln(gv.end_graph());

			//		}

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
			//		index++;
		}
	}


	public void writeGraphAsImage(CFGExplicitNode root, String fileName,
			ArrayList<IElement> error_trace) {
		
		if(m_dontWrite)
			return;
		else {
			GraphViz gv = new GraphViz();
			//		visited = new HashSet<IEdge>();
			//		graph = new StringBuilder();	
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<INode> allNodes = collectNodes(root);
			HashSet<IEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeNodesToString(allNodes).toString());
			gv.addln(writeEdgesToString(allEdges, error_trace).toString());

			gv.addln(gv.end_graph());

			//		}

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
			//		index++;
		}
	}
	
	public void writeGraphAsImage(INode root, String fileName,
			HashMap<CFGExplicitNode, CFGExplicitNode> nodeToCopy_current, 
			HashMap<CFGExplicitNode, CFGExplicitNode> nodeToCopy) {
		if(m_dontWrite)
			return;
		else {
			GraphViz gv = new GraphViz();
			locToLabel = new HashMap<String, ArrayList<String>>();

			gv.addln(gv.start_graph());

			HashSet<INode> allNodes = collectNodes(root);
			HashSet<IEdge> allEdges = collectEdges(allNodes);

			gv.addln(writeString(allNodes, allEdges, nodeToCopy_current, nodeToCopy));

			gv.addln(gv.end_graph());

			//		}

			gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
					new File(imagePath + "/" + fileName + ".png"));
			//		index++;
		}
	}

	HashSet<INode> collectNodes(INode root) {
		ArrayList<INode> openNodes = new ArrayList<INode>();
		HashSet<INode> allNodes = new HashSet<INode>(); 
		boolean hasChanged = true;

		openNodes.add(root);

		while(hasChanged) {
			hasChanged = false;

			ArrayList<INode> current_openNodes = (ArrayList<INode>) openNodes.clone();

			for(INode node : current_openNodes) {
				ArrayList<IEdge> edges = new ArrayList<IEdge>(node.getOutgoingEdges());
				if(m_showUnreachableEdges && !m_hideUnreachableOnce)
					edges.addAll(node.getIncomingEdges());

				for(IEdge e : edges) {
					INode nextNode = e.getSource();
					if(!allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						openNodes.add(nextNode);
						hasChanged = true;
					}
					nextNode = e.getTarget();
					if(!allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						openNodes.add(nextNode);
						hasChanged = true;
					}
				}
				openNodes.remove(node);
			}
		}
		return allNodes;
	}

	HashSet<IEdge> collectEdges(HashSet<INode> allNodes) {
		HashSet<IEdge> allEdges = new HashSet<IEdge>();

		for(Iterator<INode> it = allNodes.iterator(); it.hasNext();){
			for(IEdge edge : it.next().getOutgoingEdges()) {
				allEdges.add(edge);
			}
		}
		return allEdges;
	}

	StringBuilder writeNodesToString(HashSet<INode> allNodes) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<INode> it = allNodes.iterator(); it.hasNext();){
			if(m_annotateNodes) {
				graph.append(getLabeledNode(it.next()) + "\n");
			}
			else {
				graph.append(convertNodeName(it.next()) + "\n");
			}
		}

		return graph;
	}

	StringBuilder writeEdgesToString(HashSet<IEdge> allEdges) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<IEdge> it = allEdges.iterator(); it.hasNext();){
			graph.append(convertEdgeName(it.next()) + "\n");
		}

		return graph;
	}

	private Object writeEdgesToString(HashSet<IEdge> allEdges,
			ArrayList<IElement> error_trace) {
		if(error_trace == null)
			return writeEdgesToString(allEdges);
		
		StringBuilder graph = new StringBuilder(); 

		String label = "";
		
		for(Iterator<IEdge> it = allEdges.iterator(); it.hasNext();){
			IEdge current = it.next();
			if (error_trace.contains(current))
				label = "[color=blue]";
			graph.append(convertEdgeName(current) + label + "\n");
			label = "";
		}

		return graph;
	}

	
	StringBuilder writeEdgesToString(HashSet<IEdge> allEdges,
			HashMap<CFGExplicitNode, CFGExplicitNode> nodeToCopy) {
		StringBuilder graph = new StringBuilder(); 

		for(Iterator<IEdge> it = allEdges.iterator(); it.hasNext();){
			CFGEdge edge = (CFGEdge) it.next();
			graph.append(convertEdgeName(edge) + 
					(nodeToCopy.values().contains(edge.getSource()) ? " [style=dashed] " : "") 
					+ "\n");
		}

		return graph;
	}

	String writeString(HashSet<INode> allNodes, HashSet<IEdge> allEdges, 
			HashMap<CFGExplicitNode, CFGExplicitNode> nodeToCopy_current,
			HashMap<CFGExplicitNode, CFGExplicitNode> nodeToCopy) {
		StringBuilder graph = new StringBuilder(); 

		graph.append(this.writeNodesToString(allNodes));
		graph.append(this.writeEdgesToString(allEdges, nodeToCopy_current));

		for(Entry<CFGExplicitNode, CFGExplicitNode> en : nodeToCopy_current.entrySet()) {
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
			for(Entry<CFGExplicitNode, CFGExplicitNode> en : nodeToCopy.entrySet()) {
			graph.append(convertNodeName(en.getKey()) + " -> " + 
				convertNodeName(en.getValue()) + "[weight=0, color=red] ;");
			}
		}
		return graph.toString();
	}

	private String getLabeledNode(CFGExplicitNode node, String additionalOptions) {
		String quotName = convertNodeName(node);
		String name = quotName.replace("\"", "");
		String nodeLabel;
		SMTNodeAnnotations nodeAnn = 
				(SMTNodeAnnotations)node.getPayload().getAnnotations().get("SMT");
		if(nodeAnn != null) {
			Term assertion = nodeAnn.getAssertion();
			
			FormulaUnLet unLet = new FormulaUnLet();
			assertion = unLet.unlet(assertion);

			nodeLabel = "\n" + quotName 
					+ "[label = \"" + name + "\\n" + prettifyFormula(assertion) 
					+ "\" , " + additionalOptions
					+ "];" + "\n";
			//				String loc = name.split("-")[0];
			//				if(locToLabel.get(loc) == null) {
			//					ArrayList<String> al = new ArrayList<String>();
			//					al.add(nodeEntry);
			//					locToLabel.put(loc, al);
			//				}
			//				else {
			//					locToLabel.get(loc).add(nodeEntry);
			//				}
		}
		else {
			nodeLabel = quotName;
		}
		return nodeLabel;
	}


	//	void buildGraph(INode node) {
	//		ArrayList<IEdge> edges = new ArrayList<IEdge>(node.getOutgoingEdges());
	//		if(showUnreachableEdges)
	//			edges.addAll(node.getIncomingEdges());
	//		
	//		for(IEdge edge : edges) { 
	//			if(!visited.contains(edge)) {
	//				visited.add(edge);
	//				buildGraph(edge.getTarget());
	//				StringBuilder line = new StringBuilder();
	//
	//				line.append(convertNodeName(edge.getSource())
	//						+ " -> " + convertNodeName(edge.getTarget()));
	//
	//				if(annotateEdges){
	//					SMTEdgeAnnotations edgeAnn = 
	//						(SMTEdgeAnnotations)edge.getPayload().getAnnotations().get("SMT");
	//					if(edgeAnn != null) {
	//						Formula assumption = edgeAnn.getAssumption();
	//						line.append("[label=\""+ assumption + "\"]");
	//					}
	//				}
	//				line.append(";\n");
	//
	//
	//
	//				graph.append(line);
	//
	//			}
	//
	//		}
	//	}

	String convertNodeName(INode node) {
		String name = node.toString();
		//		name = "\"" + name;
		name = name.replace("[", "");
		name = name.replace("ERROR_LOCATION", "EL");
		name = name.replace("ERROR_Pseudo", "PEL");
		name = name.replace(", $Ultimate#", "");
		name = name.replace("$Ultimate#", "");
		name = name.replace("]", "");
		String sUID = node.getPayload().getID().toString();
		name = name + "-" + sUID.substring(0, sUID.length()/8);
		//		name = name + "\"";

		String quotName = "\"" + name + "\"";

		return quotName;
	}

	String getLabeledNode(INode node){
		String quotName = convertNodeName(node);
		String name = quotName.replace("\"", "");
		String nodeLabel;
		SMTNodeAnnotations nodeAnn = 
				(SMTNodeAnnotations)node.getPayload().getAnnotations().get("SMT");
		if(nodeAnn != null) {
			Term assertion = nodeAnn.getAssertion();
			
			FormulaUnLet unLet = new FormulaUnLet();
			assertion = unLet.unlet(assertion);
			
			nodeLabel = "\n" + quotName + "[label = \"" + name + "\\n" + prettifyFormula(assertion) + "\"];" + "\n";
			//				String loc = name.split("-")[0];
			//				if(locToLabel.get(loc) == null) {
			//					ArrayList<String> al = new ArrayList<String>();
			//					al.add(nodeEntry);
			//					locToLabel.put(loc, al);
			//				}
			//				else {
			//					locToLabel.get(loc).add(nodeEntry);
			//				}
		}
		else {
			nodeLabel = quotName;
		}
		return nodeLabel;
	}

	boolean m_edgesWithHash = false;

	String convertEdgeName(IEdge edge) {
		StringBuilder edgeName = new StringBuilder();
		edgeName.append(convertNodeName(edge.getSource())
				+ " -> " + convertNodeName(edge.getTarget()));

		if(m_annotateEdges){
			SMTEdgeAnnotations edgeAnn = 
					(SMTEdgeAnnotations)edge.getPayload().getAnnotations().get("SMT");
			if(edgeAnn != null) {
				Term assumption = edgeAnn.getAssumption();
				String edgeHash = m_edgesWithHash ? 
						"-"	+ edge.getPayload().getID().toString().substring(0,4) :
							"";
						edgeName.append("[label=\""+ prettifyFormula(assumption) +  edgeHash + "\"]");
			}
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
}
