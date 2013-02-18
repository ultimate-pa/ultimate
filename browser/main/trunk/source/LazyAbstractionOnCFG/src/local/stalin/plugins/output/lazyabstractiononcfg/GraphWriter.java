package local.stalin.plugins.output.lazyabstractiononcfg;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;

import local.stalin.boogie.cfgreducer.SMTEdgeAnnotations;
import local.stalin.boogie.cfgreducer.SMTNodeAnnotations;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaUnFleterer;
import local.stalin.logic.Theory;
import local.stalin.model.IEdge;
import local.stalin.model.INode;

public class GraphWriter {
	
	HashSet<IEdge> visited;
//	int index = 0;
	boolean annotateEdges = true;
	boolean annotateNodes = true;
	boolean showUnreachableEdges = true;
	boolean rankByLocation = false;
	
	StringBuilder graph;
	HashMap<String, ArrayList<String>> locToLabel;
	Theory m_theory;
	
	/*
	 * Initialize the Graphwriter with some options
	 * @param annotateEdges annotate the edges?
	 * @param annotateNodes
	 * @param showUnreachableEdges
	 * @param rankByLocation
	 */
	public GraphWriter(boolean annotateEdges, 
			boolean annotateNodes, boolean showUnreachableEdges, boolean rankByLocation, Theory theory) {
		this.annotateEdges = annotateEdges;
		this.annotateNodes = annotateNodes;
		this.showUnreachableEdges = showUnreachableEdges;
		this.rankByLocation = rankByLocation;
		m_theory = theory;
	}
	


	public void writeGraphAsImage(INode root, String fileName) {
		GraphViz gv = new GraphViz();
//		visited = new HashSet<IEdge>();
//		graph = new StringBuilder();	
		locToLabel = new HashMap<String, ArrayList<String>>();

//		boolean oldStyle = false;
//		if(oldStyle) {
//			gv.addln(gv.start_graph());
//			buildGraph(root);
//			gv.addln(graph.toString());
//
//			for(Entry<String,ArrayList<String>> locLab : locToLabel.entrySet()) {
//				if(rankByLocation){
//					gv.add(" { ");
//					gv.add("rank=same; ");
//				}
//				for(String s : locLab.getValue()) {
//					gv.add(s + "; ");
//				}
//				if(rankByLocation)
//					gv.add(" } ");
//			}
//			gv.addln(gv.end_graph());
//		}
//		else {
			
		gv.addln(gv.start_graph());
		
		HashSet<INode> allNodes = collectNodes(root);
		HashSet<IEdge> allEdges = collectEdges(allNodes);
		
		gv.addln(writeString(allNodes, allEdges));
		
		gv.addln(gv.end_graph());
		
//		}
		
		gv.writeGraphToFile( gv.getGraph( gv.getDotSource(), "png" ), 
				new File("/exchange/Studium/Masterarbeit/tmp/" + fileName + ".png"));
//		index++;
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
				if(showUnreachableEdges)
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
	
	String writeString(HashSet<INode> allNodes, HashSet<IEdge> allEdges) {
		StringBuilder graph = new StringBuilder(); 
			
		for(Iterator<INode> it = allNodes.iterator(); it.hasNext();){
			if(annotateNodes) {
				graph.append(getLabeledNode(it.next()) + "\n");
			}
			else {
				graph.append(convertNodeName(it.next()) + "\n");
			}
		}
		
		for(Iterator<IEdge> it = allEdges.iterator(); it.hasNext();){
			graph.append(convertEdgeName(it.next()) + "\n");
		}
		
		return graph.toString();
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
		name = name.replace(", $Stalin#", "");
		name = name.replace("$Stalin#", "");
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
			Formula assertion = nodeAnn.getAssertion();
			FormulaUnFleterer unFleterer = new FormulaUnFleterer(m_theory);
			assertion = unFleterer.unflet(assertion);
			nodeLabel = "\n" + quotName + "[label = \"" + name + "\\n" + assertion + "\"];" + "\n";
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
	
	String convertEdgeName(IEdge edge) {
		StringBuilder edgeName = new StringBuilder();
		edgeName.append(convertNodeName(edge.getSource())
				+ " -> " + convertNodeName(edge.getTarget()));

		if(annotateEdges){
			SMTEdgeAnnotations edgeAnn = 
				(SMTEdgeAnnotations)edge.getPayload().getAnnotations().get("SMT");
			if(edgeAnn != null) {
				Formula assumption = edgeAnn.getAssumption();
				edgeName.append("[label=\""+ assumption + "-"  
						+ edge.getPayload().getID().toString().substring(0,4) + "\"]");
			}
		}
		return edgeName.toString();
	}
}
