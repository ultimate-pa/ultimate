/**
 *
 */
package de.uni_freiburg.informatik.ultimate.plugins.safetychecker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.ConfigurationScope;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Valuation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SCNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.AbstractErrorTrace;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.FormulaArrayBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.SMTInterface;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.Const2VariableTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.safetychecker.preferences.PreferenceValues;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;
import de.uni_freiburg.informatik.ultimate.result.UnprovableResult;

/**
 * This class is the safety-checker, which goes breadth first through the reduced CFG of the Boogie PL file and checks all possible paths for feasibility.
 * 
 */

public class SafetyCheckerObserver implements IUnmanagedObserver {
	
	protected static Logger 	s_Logger 					= UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private SMTInterface		m_SMTInterface				= null;
	private CFGExplicitNode		m_Graphroot 				= null;
	private ArrayList<IElement> m_ShortestPath 				= new ArrayList<IElement>();
	private Script 				m_Script 					= null;
	private FormulaArrayBuilder m_FormulaArrayBuilder		= null;
	private ArrayList<IEdge>	m_searchStack				= new ArrayList<IEdge>();
	private int					m_checkedPaths				= 0;
	private long				m_totalTime					= 0;
	private int					m_totalSplits				= 0;
	private IEclipsePreferences m_prefs						= null;
	private boolean 			m_madeChanges				= false;
	private boolean				m_addEpsilon				= false;
	private HashSet<IElement>	m_reachableNodes			= new HashSet<IElement>();
	
//	GraphWriter gw; //inserted by alex (plus the corresponding classes)
	
	@Override
	public boolean process(IElement root) {
		m_Graphroot		= (CFGExplicitNode)root;
		m_Script		= m_Graphroot.getScript();
		m_SMTInterface = new SMTInterface(m_Script);
		m_FormulaArrayBuilder = new FormulaArrayBuilder(m_Script);
		m_prefs = ConfigurationScope.INSTANCE.getNode(Activator.PLUGIN_ID);
		
		m_addEpsilon = m_prefs.getBoolean(PreferenceValues.NAME_ACTIVATEEPSILON, PreferenceValues.VALUE_ACTIVATEEPSILON_DEFAULT);
		s_Logger.info("Epilson edges are set to " + m_addEpsilon);
		
		int maxStepNumber = m_prefs.getInt(PreferenceValues.NAME_MAXSTEPNUMBER, PreferenceValues.VALUE_MAXSTEPNUMBER_DEFAULT);
		s_Logger.info("Maximum number of iterations is set to " + maxStepNumber);
		
		//-----------------------------------------------------------------------------//		
		//------------------START SAFETY CHECKER ALGORITHM-----------------------------//
		//-----------------------------------------------------------------------------//
		m_madeChanges = false;
		
		if (m_checkedPaths != maxStepNumber) {
	
			//Checks if there is a new shortest path to an error location...
			if (!searchShortestPath_BFS()) {
				//if not then checking is finished and program proved to be correct
				PositiveResult result = new PositiveResult(null,
						Activator.PLUGIN_ID,
						UltimateServices.getInstance().getTranslatorSequence(),
						m_Graphroot.getPayload().getLocation());
				result.setShortDescription("Program is safe!");
				reportResult(result);
				s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:SAFE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			}
			else if(m_ShortestPath.size() < 2) {
				CounterExampleResult result = new CounterExampleResult(null,
						Activator.PLUGIN_ID,
						UltimateServices.getInstance().getTranslatorSequence(),
						null, null);  //TODO locations and valuation
				result.setShortDescription("Program is unsafe!");
				result.setLongDescription(m_ShortestPath.toString() + " is a real counterexample!");
				reportResult(result);
				s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:UNSAFE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			}
			else {
				//... else check new shortest path...
				s_Logger.info("Checking " + m_ShortestPath.toString());
				//step++;
				try {
					if (checkShortestPath()){
						s_Logger.info("Check succeeded for path " + m_ShortestPath.toString());
						//if path is unsatisfiable and ...
	
						//(insertion by alex): if the path is of the form (CFGRoot, edge1, ProcRoot, edge2, ErrorLocation)
						// don't split but just delete edge2
						//(became necessary when the ErrorLocationGenerator possibly does not do unsatisfiability checks) 
						if(this.m_ShortestPath.size() == 5) {
							((CFGEdge) this.m_ShortestPath.get(3)).deleteEdge();
							this.m_madeChanges = true;
							clearForNextRun();
						}
						else {
							//(end alex) (except for closing brace)
	
							if (!splitPathByInterpolants()){
								s_Logger.info("SMT solver returned an error message!");
							}
							else {
								m_madeChanges = true;
								clearForNextRun();
							}
						}
					} else {
						if (m_ShortestPath.get(m_ShortestPath.size()-1).getPayload().getName().contains("Reached_")) {
							m_reachableNodes.add(m_ShortestPath.get(m_ShortestPath.size()-3));
							deleteShortestPath();
							m_Script.pop(1);
							m_madeChanges = true;
							clearForNextRun();
						} else {
							s_Logger.info("Check failed for path " + m_ShortestPath.toString());
							//program is incorrect, stop the machinery, result notifier already called in function checkShortestPath()
						}
					}
				} catch (SMTLIBException e) {
					UnprovableResult result = new UnprovableResult(null,
							Activator.PLUGIN_ID,
							UltimateServices.getInstance().getTranslatorSequence(),
							m_Graphroot.getPayload().getLocation());
					result.setShortDescription("Check of program failed!");
					result.setLongDescription(e.getMessage() + "thrown on path \n " + m_ShortestPath.toString());
					reportResult(result);
					s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:UNKNOWN:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
					s_Logger.info(e.getMessage());
					m_Script.exit();
				}
			}
		}
		//-----------------------------------------------------------------------------//
		//------------------END SAFETY CHECKER ALGORITHM-------------------------------//
		//-----------------------------------------------------------------------------//
		
		if (!m_madeChanges) {
			s_Logger.info("Safety Checker quit after " + m_checkedPaths + " steps" + (m_checkedPaths>=maxStepNumber? " with no result!":"!"));
			dumpStatsToConsole();
		}
		clearForNextRun();
		return false;
	}	

	private void dumpStatsToConsole() {
		s_Logger.info("Reachable nodes (Empty if not activated in Error Location Generator):");
		s_Logger.info(m_reachableNodes);
		s_Logger.info("BMdata:(Safety Checker) PC#: " + m_checkedPaths);
		s_Logger.info("BMdata:(Safety Checker) TIME#: " + m_totalTime); 
		s_Logger.info("BMdata:(Safety Checker) SPLIT#: " + m_totalSplits);
		
		m_checkedPaths = 0;
		m_totalTime = 0;
	
		CFGEdge firstEdge = (CFGEdge)m_Graphroot.getOutgoingEdges().get(0);
		int edgeChecks = 0;
		long edgeChecksTime = 0;
		
		if (firstEdge != null) {
			edgeChecks = firstEdge.getTheoremProverCount();
			edgeChecksTime = firstEdge.getTotalTime();
		}
		
		s_Logger.info("BMdata:(Edge Checks) EC#: " + edgeChecks);
		s_Logger.info("BMdata:(Edge Checks) TIME#: " + edgeChecksTime);
		
		((CFGEdge)m_Graphroot.getOutgoingEdges().get(0)).resetStats();
	}
	
	private void clearForNextRun(){
		m_ShortestPath.clear();
	}
	
	// alternative search with BFS
	private boolean searchShortestPath_BFS() {
		m_searchStack.clear();
		for (IEdge e: m_Graphroot.getOutgoingEdges()) {
			m_searchStack.add(e);
			if (e.getTarget().getPayload().getName().contains("ERROR")){
				buildErrorPath(m_searchStack.size()-1);
				return true;
			}
		}
		
		int i = 0;
		// if the search stack still holds edges that might lead to an error continue...
		while(i < m_searchStack.size()) {
			// get the current node which will be expanded
			
			INode node = m_searchStack.get(i).getTarget();
			// run through all descendants... 
			for(IEdge e: node.getOutgoingEdges()) {
				INode target = e.getTarget();
				// check if descendant has already been visited by another path(shorter path by construction of BFS)
				if (getNodeFromSearchStack(target)  < 0) {
					// append new edge to search stack since descendant has not been visited yet
					m_searchStack.add(e);
					// check if descendant is an error node
					if (target.getPayload().getName().contains("ERROR")) {
						buildErrorPath(m_searchStack.indexOf(e));
						return true;
					}
				}
			}
			i++;
		}
		return false;
	}
	
	// builds the error path by backtracking through search stack
	private void buildErrorPath(int errorIndex) {
		int i = errorIndex;
		while (i >= 0){ 
			IEdge e = m_searchStack.get(i);
			m_ShortestPath.add(0, e.getTarget());
			m_ShortestPath.add(0, e);
			i = getNodeFromSearchStack(e.getSource());
		}
		m_ShortestPath.add(0, m_Graphroot);
	}
	
	// returns the index of the edge in the search stack that leads to the node else returns -1
	private int getNodeFromSearchStack(INode node) {
		for (IEdge e: m_searchStack) {
			if (e.getTarget() == node) {
				return m_searchStack.indexOf(e);
			}
		}
		return -1;
	}
	
	//returns true if path is unsatisfiable
	private boolean checkShortestPath() {
		boolean foundErrorPath = false;
		//Checking whether shortest path has any nodes with self-loops; this is set by function searchShortestPath()

		/*shortest path has at least one self-looping node and therefore must be separated to node-edge pairs
		 * in order to gain interpolants for splitting which is done by function getFormulas()*/
		//getting separated formulas from getFormulas()
		Term[] formulas = m_FormulaArrayBuilder.getFormulas(m_ShortestPath);
		//dumps formula to a designated file
		Term[] interpolants = null;
		//naming terms to find actual error trace if path is feasible

		//getting interpolants from SMT interface
		if (formulas.length == 1){
			// procedure has no loops and therefore error path is a single edge
			// result must be initialized because null means UNSAT 
			Term[] result = new Term[]{};
			try {
				long startTime = System.currentTimeMillis();
				result = m_SMTInterface.computeInterpolants(formulas);
				m_totalTime += (System.currentTimeMillis() - startTime);
			} catch (SMTLIBException e) {
				if (e.getMessage().equals("Logical context not inconsistent!")) {
					interpolants = null;	
				} else {
					throw e;
				}
			}
			
			if (result == null){
				// procedure is unsafe
				foundErrorPath = true;
			} else {
				/* Procedure is safe but path can not be split; therefore deleting edge;
				 * If there are no other procedure left, safety checker won't find error
				 * path in next step and program is safe
				 */
				((CFGEdge)m_ShortestPath.get(1)).deleteEdge();
			}
		} else {
			// procedure has loops and therefore must be split by interpolants if unsat
			
			try {
				long startTime = System.currentTimeMillis();
				interpolants = m_SMTInterface.computeInterpolants(formulas);
				m_totalTime += (System.currentTimeMillis() - startTime);
			} catch (SMTLIBException e) {
				if (e.getMessage().equals("Logical context not inconsistent!")) {
					interpolants = null;
				}
				else {
					throw e;
				}
			}

			if (interpolants == null) {				
				foundErrorPath = true;
			}
		}
		m_checkedPaths++;
		
		//Check if SMT interface returned valid result ...
		if (foundErrorPath){
			if (!(m_ShortestPath.get(m_ShortestPath.size()-1).getPayload().getName().contains("Reached"))) {
//				ArrayList<String> eventSequence = new ArrayList<String>();
//				for (IElement element: m_ShortestPath) {
//					if (element instanceof INode) {
//						String name = element.getPayload().getName();
//						if (name.contains("Event")) {
//							name = (String) name.subSequence(1, name.indexOf("_"));
//							eventSequence.add(name);
//						}
//					}
//				}
//				if (!(eventSequence.isEmpty()))
//					s_Logger.info("Event Sequence: " + eventSequence.toString());
//				
				ErrorTrace errorTrace = new ErrorTrace(m_Script, m_ShortestPath, formulas);
				HashMap<BoogieVar, Term> inputVariables = m_FormulaArrayBuilder.getInputVariables();
				Term[] input = new Term[inputVariables.size()];
				inputVariables.values().toArray(input); //Throws ArrayStoreException
				Valuation valuation = m_Script.getValue(input);
				s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-Initial Values-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
				s_Logger.info(valuation);
				m_Script.pop(1);
				
				s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-ERROR TRACE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
				if (errorTrace.isEmpty()) {
					s_Logger.info("Was not able to build error trace. Check if Edge IDs are switch on in preference page.");
					CounterExampleResult cexResult = new CounterExampleResult(
							null,
							Activator.PLUGIN_ID,
							UltimateServices.getInstance().getTranslatorSequence(),
							m_ShortestPath.get(m_ShortestPath.size()-1).getPayload().getLocation(), null);
					this.reportResult(cexResult);
				} else {
					this.reportResult(errorTrace.getCounterExampleResult());
					for (int i = 0; i < errorTrace.getLocations().size(); i++) {
						ILocation l = errorTrace.getLocations().get(i);
						s_Logger.info(l.getStartLine() + "," + l.getEndLine());
					}
					try {
						AbstractErrorTrace abstractErrorTrace = new AbstractErrorTrace(errorTrace, null, null);
						
						s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:ABSTRACT ERROR TRACE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
						if (abstractErrorTrace.isEmpty()) {
							s_Logger.info("Was not able to compress error trace because smt solver returned no interpolants. Can be caused by havoc statements.");
						} else {
							CounterExampleResult cexResult = 
									(CounterExampleResult) abstractErrorTrace.getCounterExampleResult();
							cexResult.setShortDescription("Abstract Error Trace.");
							this.reportResult(cexResult);
							for (int i = 0; i < abstractErrorTrace.getLocations().size(); i++) {
								ILocation l = abstractErrorTrace.getLocations().get(i);
								s_Logger.info(l.getStartLine() + "," + l.getEndLine());
							}
						}
					}
					catch(IllegalArgumentException e) {
						s_Logger.info(e.getMessage());
					}
				}
				s_Logger.info("!:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:UNSAFE:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-:-!");
			}
			return false;
		}

		//add newly obtained interpolants to the payload of the corresponding nodes because they will be needed explicitly for splitting
	
		for (int i = 4; i < m_ShortestPath.size()-2; i+=2){
			CFGExplicitNode node = (CFGExplicitNode)m_ShortestPath.get(i);
			SCNodeAnnotations scAnnotations = (SCNodeAnnotations)node.getPayload().getAnnotations().get("SC");
			if (scAnnotations == null){
				scAnnotations = new SCNodeAnnotations(m_Script.term("true"));
				node.getPayload().getAnnotations().put("SC", scAnnotations);
			}
			Term tmp_interpolant = interpolants[i/2-2];
			// reverts all substitute variables of the interpolant to the correct variables of the specific node
			Const2VariableTermTransformer C2VTermTransformer = new Const2VariableTermTransformer(scAnnotations.getConstants(),
					m_FormulaArrayBuilder.getConstantsToBoogieVariableMap(), node, m_Script);
			Term interpolant = C2VTermTransformer.transform(tmp_interpolant);
			Term invariant = null;
			//get old invariant of this node
			Term old_invariant = scAnnotations.getInvariant();
			//Check if there was an old invariant ...
			if (old_invariant == null){
				//no old invariant found, therefore new interpolant is first invariant of this node
				invariant = interpolant;
			} else {
				//old invariant found, therefore appending new interpolant to old invariant by conjunction
				invariant = m_Script.term("and", interpolant, old_invariant);
			}
			//putting new interpolant and invariant in payload of node
			scAnnotations.setInvariant(invariant);
			scAnnotations.setInterpolant(interpolant);
		}
		return true;
	}

	//splits all inner nodes on the path and extends their assertions with corresponding interpolants
	private boolean splitPathByInterpolants(){
		ArrayList<CFGExplicitNode> allTouchedNodes = new ArrayList<CFGExplicitNode>();
		boolean result = true;
		//iterates through all inner nodes of the path and splits them
		for (int i = 4; i < m_ShortestPath.size()-1; i += 2){
			//get assertion and interpolant of node
			CFGExplicitNode node = (CFGExplicitNode)m_ShortestPath.get(i);
			SCNodeAnnotations	scAnnotations		= (SCNodeAnnotations)node.getPayload().getAnnotations().get("SC");
			SMTNodeAnnotations	smtNodeAnnotations	= node.getSMTAnnotations();
			
			Term assertion	= smtNodeAnnotations.getAssertion();
			Term interpolant = scAnnotations.getInterpolant();
			//Create new node for splitting
			CFGExplicitNode		splitNode				= node.copyWithoutEdges();
			m_totalSplits++;
			//MTNodeAnnotations	smtCopyNodeAnnotations	= splitNode.getSMTAnnotations();
			//append interpolant to the assertions
			node.setAssertion(m_Script.term("and", assertion, interpolant));
			splitNode.setAssertion(m_Script.term("and", assertion, m_Script.term("not", interpolant)));
			//Run SSA on splitNodes annotation
			splitNode.getSMTAnnotations().useSSA();
			//copy all in- and outgoing edges of original node
			splitNode.copyAllPredecessorsFromNode(node);
			splitNode.copyAllSuccessorsFromNode(node);
			//this should be unnecessary because error-edge should be unsatisfiable anyway
			CFGEdge errorEdge = null;
			
			for (IEdge iedge: node.getOutgoingEdges()){
				if(iedge.getTarget().getPayload().getName().contains("ERROR")){
					errorEdge = (CFGEdge)iedge;
				} else if (iedge.getTarget() == splitNode) {
					if (m_addEpsilon){
						s_Logger.info("Added epsilon alternative to edge " + iedge.getPayload().getName());
						((CFGEdge)iedge).addIdentityAlternative();
					}
				}
			}
			if (errorEdge != null)
				errorEdge.deleteEdge();
			//collect all edges of both nodes for slicing step
			allTouchedNodes.add(node);
			allTouchedNodes.add(splitNode);
//			result = result && node.cleanUnsatisfiableEdges();
//			splitNode.cleanUnsatisfiableEdges();
			
			//remove nodes that have no effect on the loops or the error paths anymore
//			if (node.getOutgoingEdges().size() == 0) {
//				node.removeAllIncoming();
//			}
//			if (splitNode.getOutgoingEdges().size() == 0) {
//				splitNode.removeAllIncoming();
//			}
		}
		result = slice(allTouchedNodes);
		return result;
	}
	
	private boolean slice(ArrayList<CFGExplicitNode> nodes) {
		boolean result = true;
		ArrayList<IEdge> allCheckedIncomingEdges = new ArrayList<IEdge>();
		ArrayList<IEdge> allUncheckedOutgoingEdges = new ArrayList<IEdge>();
		for (CFGExplicitNode node: nodes) {
			result &= node.cleanUnsatisfiableIncomingEdges();
			allCheckedIncomingEdges.addAll(node.getIncomingEdges());
			allUncheckedOutgoingEdges.addAll(node.getOutgoingEdges());
		}
		allUncheckedOutgoingEdges.removeAll(allCheckedIncomingEdges);
		result &= deleteUnsatisfiableEdges(allUncheckedOutgoingEdges);
		return result;
	}
	
	private boolean deleteUnsatisfiableEdges(ArrayList<IEdge> edges){
		ArrayList<CFGEdge> unsatEdges = new ArrayList<CFGEdge>();
		ArrayList<IEdge> redundantEdgeChecks = new ArrayList<IEdge>();
		for (IEdge iEdge: edges){
			if (redundantEdgeChecks.contains(iEdge)) {
				continue;
			}
			CFGEdge edge = (CFGEdge)iEdge;
			LBool result;
			try {
				result = edge.checkSatisfiability();
			} catch (SMTLIBException e) {
				s_Logger.info("Failed cleaning unsat outgoing edge " + edge.getPayload().getName());
				s_Logger.info(e);
				return false;
			}
			if (result == LBool.UNSAT){ // -1 is unsat
				unsatEdges.add(edge);
				if (edge.getTarget().getIncomingEdges().isEmpty()) {
					redundantEdgeChecks.addAll(edge.getTarget().getIncomingEdges());
				}
			}
		}
		
		for (CFGEdge edge: unsatEdges){
			edge.deleteEdge();
		}
		return true;
	}
	
	//deletes the path as far as possible
	private void deleteShortestPath() {
		deletePath(m_ShortestPath);
	}
	
	//deletes the given path as far as possible
	private void deletePath(ArrayList<IElement> path){
		if (!(path.size() < 3)){
			CFGExplicitNode node = (CFGExplicitNode)path.get(path.size()-1);
			if (node.getOutgoingEdges().size() < 1){
				CFGEdge edge = (CFGEdge)path.get(path.size()-2);
				edge.deleteEdge();
				for(int i=0;i<2;i++){
					path.remove(path.size()-1);
				}
				this.deleteShortestPath();
			}
		}
		path.clear();
		return;
	}
	
	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.PLUGIN_ID, res);
	}
	
	
	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean performedChanges() {
		return m_madeChanges;
	}
}
