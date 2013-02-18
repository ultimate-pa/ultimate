package local.stalin.boogie.newgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import local.stalin.access.IUnmanagedObserver;
import local.stalin.access.WalkerOptions;
import local.stalin.core.api.StalinServices;
import local.stalin.model.IElement;
import local.stalin.model.INode;
import local.stalin.model.boogie.ast.Axiom;
import local.stalin.model.boogie.ast.ConstDeclaration;
import local.stalin.model.boogie.ast.Declaration;
import local.stalin.model.boogie.ast.FunctionDeclaration;
import local.stalin.model.boogie.ast.GotoStatement;
import local.stalin.model.boogie.ast.Label;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.Statement;
import local.stalin.model.boogie.ast.TypeDeclaration;
import local.stalin.model.boogie.ast.Unit;
import local.stalin.model.boogie.ast.VariableDeclaration;
import local.stalin.model.boogie.ast.wrapper.WrapperNode;

import org.apache.log4j.Logger;

/**
 * This Class is a BoogieAst Visitor for creating a graph representation of the
 * BoogieAST. It return a control flow graph.
 */

public class CFGBuilderObserver implements IUnmanagedObserver {

	private static final Boolean debugMessages = false;
	/**
	 * @param s_Logger
	 *            Output to console
	 */
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	/**
	 * @param labelMap
	 *            contains all visited LabelStatements. They're represented by
	 *            the label string as key and their corresponding CFG Node.
	 */
	private HashMap<String, CFGNode> labelMap = new HashMap<String, CFGNode>();
	/**
	 * @param gotoMap
	 *            contains all visited GotoStatements whose corresponding Label
	 *            hasn't been visited yet. Each time a LabelStatement is found
	 *            there will be a lookup in gotoMap and edges will be added
	 *            respectively. After that all resolved GotoStatements will be
	 *            removed from gotoMap.
	 */
	private HashMap<String, List<CFGNode>> gotoMap = new HashMap<String, List<CFGNode>>();
	/**
	 * @param graphroot
	 *            Top most node of the CFG.
	 */
	private static CFGNode graphroot = new CFGNode();

	/**
	 * 
	 * @return the root of the CFG.
	 */
	public INode getRoot(){
		return CFGBuilderObserver.graphroot;
	}
	
	/**
	 * Called by the Stalin Framework. Finds all procedure declarations and
	 * checks whether they're implementations or just declarations. If
	 * implementation is present calls makeProcedureCFG() and appends CFG as
	 * child of procedure node to CFG
	 */
	// @Override
	public boolean process(IElement root) {
		if (root instanceof WrapperNode) {
			graphroot = new CFGNode();
			graphroot.getPayload().setName("CFGRoot");
			graphroot.getPayload().setLocation(root.getPayload().getLocation());
			
			CFGRootAnnotations annotations = new CFGRootAnnotations();
			graphroot.getPayload().getAnnotations().put("CFGBuilder", annotations);

			Unit unit = (Unit) ((WrapperNode)root).getBacking();
			if(debugMessages) CFGBuilderObserver.s_Logger.info("--Starting to look for all procedures in code--");
		
			for (Declaration d : unit.getDeclarations()){
				if (d instanceof TypeDeclaration
					|| d instanceof FunctionDeclaration
					|| d instanceof ConstDeclaration
					|| d instanceof VariableDeclaration) {
					annotations.addDeclaration(d);
				} else if (d instanceof Axiom){
					annotations.addAxiom((Axiom) d);
				} else if (d instanceof Procedure){
					Procedure proc = (Procedure) d;
					if (proc.getSpecification() != null)
						annotations.addDeclaration(proc);

					if (proc.getBody() != null) {
						if(debugMessages) CFGBuilderObserver.s_Logger.info("--Found Procedure -> starting to make CFG--");

						CFGNode entryNode = new CFGNode(graphroot);
						entryNode = this.makeProcedureCFG((Procedure) d);
						CFGBuilderObserver.graphroot.addOutgoingNode(entryNode);
					}
				}
			}
			if(debugMessages) CFGBuilderObserver.s_Logger.info("--Found all procedures and made CFGs--");
			return false;
		}
		return true;
	}

	/**
	 * Iterates through all statements in the block of the current procedure. If
	 * current statement is a goto statement then checks whether label already
	 * resolved or not. If label resolved(in labelMap) then make connections
	 * otherwise add goto statement to gotoMap. If current statement is a label
	 * statement then
	 * 
	 * @param p
	 *            is the current procedure whose CFG will be made
	 * @return the entry node of the CFG of the procedure p
	 * @see labelMap
	 * @see gotoMap
	 */
	private CFGNode makeProcedureCFG(Procedure p){
		CFGNode cfgRoot = makeCFG(p.getIdentifier());
		cfgRoot.getCFGAnnotations().setProcedure(p);
		
		if(debugMessages){
			CFGBuilderObserver.s_Logger.info("Procedure Found: " + p.getIdentifier());
			if (p.getSpecification() == null){
				CFGBuilderObserver.s_Logger.info("This is not a procedure but an implementation!");
			}
		}
		CFGNode lastCFGNode = cfgRoot;
		for ( int i =0; i<p.getBody().getBlock().length; i++ ){
			Statement statement = p.getBody().getBlock()[i];
			if(debugMessages) CFGBuilderObserver.s_Logger.info("--------->New statement: " + statement.toString());

			if (statement instanceof GotoStatement){
				//lastCFGNode.setHasSuccessor(true);
				if(debugMessages){
					String labelnames = "";
					for (String s: ((GotoStatement)statement).getLabels()){
						labelnames += s + " ";
					}
					CFGBuilderObserver.s_Logger.info("Found GotoStatement: " + labelnames);
				}
				for (String label : ((GotoStatement)statement).getLabels()) {
					CFGNode tmp = new CFGNode();
					tmp = findLabeledNode(label);
					if (tmp != null){
						if(debugMessages) CFGBuilderObserver.s_Logger.info("Labeled Node already exists: " + label);
						lastCFGNode.addOutgoingNode(tmp);
						tmp.addIncomingNode(lastCFGNode);
					} else {
						if(debugMessages) CFGBuilderObserver.s_Logger.info("Labeled Node does not exist. Adding to gotoMap: " + label);
						this.addToGotoMap(label, lastCFGNode);
					}
				}	
				//lastCFGNode = null;

			} else if (statement instanceof Label){
				List<String> equalLabels = new ArrayList<String>();
				while (i < p.getBody().getBlock().length && p.getBody().getBlock()[i] instanceof Label){
					equalLabels.add(((Label)p.getBody().getBlock()[i]).getName());
					i++;
				}
				CFGNode newCFGNode = makeCFG(equalLabels.toString());
				if (lastCFGNode == cfgRoot) {
					cfgRoot.addOutgoingNode(newCFGNode);
					newCFGNode.addIncomingNode(cfgRoot);
				}
				lastCFGNode = newCFGNode;
				if(i < p.getBody().getBlock().length && debugMessages) CFGBuilderObserver.s_Logger.info("--------->New statement: " + p.getBody().getBlock()[i].toString());
				if(debugMessages) CFGBuilderObserver.s_Logger.info("Made new CFGNode: " + lastCFGNode.getPayload().getName());
				for (String label: equalLabels){
					this.addToLabelMap(label, lastCFGNode);
				}

				if(debugMessages) CFGBuilderObserver.s_Logger.info("Found new Label and added to labelMap: " + equalLabels.toString());
				for (String label: equalLabels){
					for (CFGNode gotoNode: this.findGotoNode(label)){
						gotoNode.addOutgoingNode(lastCFGNode);
						lastCFGNode.addIncomingNode(gotoNode);
						if(debugMessages) CFGBuilderObserver.s_Logger.info("Added Edge from " + gotoNode.getPayload().getName() + " to this Label: " + label);
					}
				}
				i--;

			} else {
				if(debugMessages) CFGBuilderObserver.s_Logger.info("Found Statement: " + statement.toString());
				/*if (statement instanceof ReturnStatement){
					lastCFGNode.setHasSuccessor(true);				
				}*/
				lastCFGNode.addStatementToNode(statement);
				if(debugMessages) CFGBuilderObserver.s_Logger.info(lastCFGNode.getPayload().getName() + ": Added Statement " + statement.toString());
			}					
		}
		/*if (!lastCFGNode.getHasSuccessor()) {
			CFGBuilderObserver.s_Logger.info(lastCFGNode.getPayload().getName() + " has no outgoing edges!");
			lastCFGNode.addStatementToNode(new ReturnStatement(lastCFGNode.getPayload().getLocation().getFileName(), -1));
		}*/
		this.clearMaps();
		return cfgRoot;
	}

	private CFGNode makeCFG(String name){
		CFGNode newNode = new CFGNode();
		newNode.getPayload().getAnnotations()
			.put("CFGBuilder", new CFGNodeAnnotations());
		newNode.setName(name);
		return newNode;
	}
	
	private void addToLabelMap(String label, CFGNode node){
		this.labelMap.put(label,node);
	}

	private void addToGotoMap(String label, CFGNode node){
		List<CFGNode> nodeList = new ArrayList<CFGNode>();
		
		if (gotoMap.containsKey(label)){
			nodeList = gotoMap.get(label);
		}
		
		nodeList.add(node);
		this.gotoMap.put(label, nodeList);
	}
	
	private CFGNode findLabeledNode(String label){
		try{
			return this.labelMap.get(label);
		} catch (Exception e){
			return null;
		}
	}
	
	private List<CFGNode> findGotoNode(String label){
		List<CFGNode> gotoNodes = new ArrayList<CFGNode>();
		
		if (gotoMap.containsKey(label)){
			gotoNodes = gotoMap.get(label);
		}
		return gotoNodes;
	}
	
	private void clearMaps(){
		this.labelMap.clear();
		this.gotoMap.clear();
	}
	
	// @Override
	public void finish() {
	}

	// @Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	// @Override
	public void init() {
	}

	@Override
	public boolean performedChanges() {
		// TODO Replace with a decent implementation!
		return getDefaultPerformedChanges();
	}

	@Deprecated
	private boolean getDefaultPerformedChanges() {
		return false;
	}

}
