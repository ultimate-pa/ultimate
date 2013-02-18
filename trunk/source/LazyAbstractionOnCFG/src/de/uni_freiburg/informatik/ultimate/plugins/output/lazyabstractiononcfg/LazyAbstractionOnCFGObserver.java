package de.uni_freiburg.informatik.ultimate.plugins.output.lazyabstractiononcfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SCNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace.ErrorTrace;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.FormulaArrayBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils.SMTInterface;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.Const2VariableTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.output.lazyabstractiononcfg.preferences.PreferenceConstants;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.PositiveResult;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class LazyAbstractionOnCFGObserver implements IUnmanagedObserver {

	private static Logger s_logger = UltimateServices.getInstance().getLogger(
			Activator.s_PLUGIN_ID);

	private FormulaArrayBuilder m_formulaArrayBuilder = null;
	private SMTInterface m_SMTInterface = null;
	private Script m_script = null;

	private boolean m_performedChanges = false;

	private boolean debugOutput = true;

	private long m_totalTime = 0;
	private int m_checkedPaths = 0;

	private HashMap<CFGExplicitNode, CFGExplicitNode> m_nodeToCopy = 
			new HashMap<CFGExplicitNode, CFGExplicitNode>();
	private HashMap<CFGExplicitNode, CFGExplicitNode> m_nodeToCopy_current = 
			new HashMap<CFGExplicitNode, CFGExplicitNode>();
	private HashMap<CFGExplicitNode, CFGExplicitNode> m_copyToOriginal = 
			new HashMap<CFGExplicitNode, CFGExplicitNode>();
	private HashMap<CFGExplicitNode, CFGExplicitNode> m_copyToNode_current = 
			new HashMap<CFGExplicitNode, CFGExplicitNode>();

	private ArrayList<IElement> m_copied_error_trace;

	private boolean deleteFalseNodes = true;
	private boolean checkPELEdges = true; // upon creation of a PEL: if the edge is
									// valid, delete it

	/**
	 * entry point for this class, make one refinement step in the CEGAR-Loop
	 * sets m_performedChanges
	 */
	@Override
	public boolean process(IElement root) {
		s_logger.debug(" --------------- LazyAbstractionOnCFG starting ------------------ ");
		s_logger.debug("for the " + m_checkedPaths + "th time");
		CFGExplicitNode cfgRoot;

		if (root instanceof CFGExplicitNode) {
			cfgRoot = (CFGExplicitNode) root;
		} else {
			s_logger.error("LazyAbstractionONCFG only runs on the output of ErrorLocationGenerator");
			return false;
		}

		m_script = cfgRoot.getScript();

		m_SMTInterface = new SMTInterface(m_script);
		if (m_SMTInterface == null)
			s_logger.debug("UltimateServices failed to store solver object!");

		m_formulaArrayBuilder = new FormulaArrayBuilder(m_script);

		GraphWriter gw = new GraphWriter(Activator.getDefault().getPreferenceStore()
				.getString(PreferenceConstants.P_IMAGE_PATH), Activator
				.getDefault().getPreferenceStore()
				.getBoolean(PreferenceConstants.P_ANNOTATE_EDGES), Activator
				.getDefault().getPreferenceStore()
				.getBoolean(PreferenceConstants.P_ANNOTATE_NODES), Activator
				.getDefault().getPreferenceStore()
				.getBoolean(PreferenceConstants.P_SHOW_UNREACHABLE), false,
				m_script);

		cleanUpGraph(cfgRoot);

		int procCount = cfgRoot.getOutgoingEdges().size();
		
		boolean unsafeOrUnknown = false;
		for (int i = 0; i < procCount; i++) {
			CFGExplicitNode procRoot = (CFGExplicitNode) cfgRoot
					.getOutgoingEdges().get(i).getTarget();
			if (procRoot.getOutgoingEdges().size() == 0) {
				if (procRoot.getPayload().getName().contains("ERROR")) {
					gw.writeGraphAsImage(cfgRoot, "graph_0"); 
					
					ArrayList<IElement> errorTrace = new ArrayList<IElement>();
					errorTrace.add(cfgRoot);

					CFGEdge edge = new CFGEdge(m_script, m_script.term("true"), 
							cfgRoot, procRoot);
					procRoot.addIncomingEdge(edge);
					cfgRoot.addOutgoingEdge(edge);
					errorTrace.add(edge);
					errorTrace.add(procRoot);
					
					//HACK: we know unsafe from ELG, but the ELG has popped...
					//we also need getFormulas for the SCAnnotations
					Term[] itps = m_SMTInterface.computeInterpolants(
							m_formulaArrayBuilder.getFormulas(errorTrace));
					assert itps == null;
					
					Term[] errorTraceFormulas = new Term[errorTrace.size()-2];
					IElement el = errorTrace.get(2);
					errorTraceFormulas[0] = ((CFGExplicitNode)el).getAssertion();
					
					reportUnsafe(errorTrace, errorTraceFormulas);
					
					unsafeOrUnknown = true;
					break;
				}
			}
		}

		int maxStepNumber = Activator.getDefault().getPreferenceStore()
				.getInt(PreferenceConstants.P_MAX_STEPS);

		this.m_performedChanges = false;

		if (this.m_checkedPaths < maxStepNumber && !unsafeOrUnknown) {
			s_logger.debug("starting on new CFG");
			gw.setHideUnreachableOnce(true);
			gw.writeGraphAsImage(cfgRoot, "graph_" + this.m_checkedPaths
					+ "_a0_repeat");
			gw.setHideUnreachableOnce(false);

			ArrayList<IElement> error_trace = searchShortestPath_BFS(cfgRoot);

			gw.setHideUnreachableOnce(true);
			gw.writeGraphAsImage(cfgRoot, "graph_" + this.m_checkedPaths
					+ "_a_repeat", error_trace);
			gw.setHideUnreachableOnce(false);

			// If there is no path to the Error Location, we are done. Otherwise
			// refine the abstraction.
			if (error_trace == null) {
				PositiveResult result = new PositiveResult(null,
						Activator.s_PLUGIN_NAME,
						UltimateServices.getInstance().getTranslatorSequence(),
						cfgRoot.getPayload()
						.getLocation());
				result.setShortDescription("Program is safe!");
				reportResult(result);
				s_logger.info("-------------- P R O G R A M   S A F E -----------------");
				// this.m_performedChanges = false;
			} else {
				boolean isPELtrace = false;
				if (error_trace.get(error_trace.size() - 1).getPayload()
						.getName().contains("ERROR_Pseudo"))
					isPELtrace = true;
				Term[] formulas = m_formulaArrayBuilder.getFormulas(error_trace);
				// if the error path is of the form (CFGRoot, edge1, procRoot,
				// edge2, ErrorLocation),
				// it is too short for copying, just delete edge2, once it has
				// been refuted (which is at this point)
				if (error_trace.size() == 5) {
					Term[] interpolants = getInterpolantsFromFormulas(formulas);
					if (interpolants == null) {
						if (isPELtrace) {
							((CFGEdge) error_trace.get(error_trace.size() - 2))
									.deleteEdge();
							m_script.pop(1);
							m_performedChanges = true;
							return false;
						}
						reportUnsafe(error_trace, formulas);
					} else {
						((CFGEdge) error_trace.get(3)).deleteEdge();
						this.m_performedChanges = true;
					}
				} else {

					Term[] interpolants = getInterpolantsFromFormulas(formulas);

					if (interpolants == null) {
						if (isPELtrace) {
							((CFGEdge) error_trace.get(error_trace.size() - 2))
									.deleteEdge();
							m_script.pop(1);
							m_performedChanges = true;
							return false;
						}
						reportUnsafe(error_trace, formulas);
					} else {
						this.m_nodeToCopy_current = new HashMap<CFGExplicitNode, CFGExplicitNode>();
						this.m_copyToNode_current = new HashMap<CFGExplicitNode, CFGExplicitNode>();

						copyNodes(cfgRoot, error_trace, interpolants);
						gw.writeGraphAsImage(cfgRoot, "graph_"
								+ (this.m_checkedPaths - 1) + "_b_copied",
								m_nodeToCopy_current, m_nodeToCopy);

						redirectEdgesOnNewErrorPath(error_trace);

						deleteNewErrorEdge(cfgRoot, error_trace);
						gw.writeGraphAsImage(cfgRoot,
								"graph_" + (this.m_checkedPaths - 1)
										+ "_c_noTPbendings",
								m_nodeToCopy_current, m_nodeToCopy);

						redirectEdges(error_trace, isPELtrace);
						gw.writeGraphAsImage(cfgRoot, "graph_"
								+ (this.m_checkedPaths - 1) + "_d_redirected",
								m_nodeToCopy_current, m_nodeToCopy);

						if (deleteFalseNodes) {
							CFGExplicitNode falseNode = new CFGExplicitNode(
									m_script, m_script.term("false"));
							ArrayList<CFGExplicitNode> nodesToRemove = new ArrayList<CFGExplicitNode>();
							for (CFGExplicitNode n : m_nodeToCopy_current
									.values()) {
								CFGEdge newEdge = new CFGEdge(m_script,
										m_script.term("true"), n, falseNode);
								LBool result = newEdge.checkValidity();
								newEdge.deleteEdge();
								if (result == LBool.UNSAT) {
									nodesToRemove.add(n);
								}
							}
							disconnectNodes(nodesToRemove);
							gw.writeGraphAsImage(cfgRoot, "graph_"
									+ (this.m_checkedPaths - 1)
									+ "_e_deletedFalse", m_nodeToCopy_current,
									m_nodeToCopy);
						}
					}
				}
			}
		}

		if (!this.m_performedChanges) {
			s_logger.info("LAonCFG quit after "
					+ m_checkedPaths
					+ " steps"
					+ (m_checkedPaths >= maxStepNumber ? " with no result!"
							: "!"));
			logStats(cfgRoot);
		}

		return false;
	}	

	private void reportUnsafe(ArrayList<IElement> error_trace, Term[] formulas) {
		ErrorTrace errorTrace = new ErrorTrace(m_script, error_trace, formulas);
		this.reportResult(errorTrace.getCounterExampleResult());
		
		s_logger.info("-------------- P R O G R A M   U N S A F E -----------------");
	}

	private Term[] getInterpolantsFromFormulas(Term[] formulas) {
		// compute whether path is infeasible and interpolants if possible
		long startTime = System.currentTimeMillis();
		Term[] interpolants = m_SMTInterface.computeInterpolants(formulas);
		m_totalTime += (System.currentTimeMillis() - startTime);
		m_checkedPaths++;

		if (debugOutput) {
			StringBuilder sb = new StringBuilder();
			for (int i = 0; i < formulas.length; i++)
				sb.append(formulas[i] + "\n");
			s_logger.debug("computed interpolants for: \n" + sb);
			if (interpolants != null) {
				sb = new StringBuilder();
				for (int i = 0; i < interpolants.length; i++)
					sb.append(interpolants[i] + "\n");
				s_logger.debug("resulting interpolants: \n" + sb);
			}
		}
		return interpolants;
	}

	private void disconnectNodes(ArrayList<CFGExplicitNode> nodesToRemove) {
		ArrayList<CFGEdge> edgesToRemove = new ArrayList<CFGEdge>();
		for (CFGExplicitNode n : nodesToRemove) {
			for (IEdge e : n.getIncomingEdges()) {
				edgesToRemove.add(((CFGEdge) e));
			}
			for (IEdge e : n.getOutgoingEdges()) {
				edgesToRemove.add(((CFGEdge) e));
			}

			// when a node is disconnected, remove it from the nodeToCopy map,
			// too
			m_nodeToCopy.remove(n);
		}
		for (CFGEdge e : edgesToRemove)
			e.deleteEdge();
	}

	/**
	 * make a copy of each node along the error trace, its assertion is
	 * strengthened with the interpolant, don't bother with incoming edges, but
	 * duplicate outgoing edges
	 * 
	 * @param cfgRoot
	 * @param error_trace
	 * @param interpolants
	 */
	private void copyNodes(CFGExplicitNode cfgRoot,
			ArrayList<IElement> error_trace, Term[] interpolants) {
		for (int i = 4; i < error_trace.size() - 1; i += 2) {
			CFGExplicitNode node = (CFGExplicitNode) error_trace.get(i);

			if (!node.getAssertion().equals(m_script.term("true"))
					&& !node.getAssertion().equals(m_script.term("false"))
					&& node.getSMTAnnotations().getVars().isEmpty())
				assert false;
			assert interpolants.length == error_trace.size() / 2 - 1;

			CFGExplicitNode copy = node.copyWithoutEdges();

			Term tmp_interpolant = interpolants[i / 2 - 2];

			SCNodeAnnotations scAnnotations = (SCNodeAnnotations) node
					.getPayload().getAnnotations().get("SC");

			// reverts all substitute variables of the interpolant to the
			// correct variables of the specific node
			Const2VariableTermTransformer C2VTermTransformer = new Const2VariableTermTransformer(
					scAnnotations.getConstants(),
					m_formulaArrayBuilder.getConstantsToBoogieVariableMap(),
					copy, m_script);
			Term interpolant = C2VTermTransformer.transform(tmp_interpolant);

			Term newFormula = Util.and(m_script, copy.getAssertion(),
					interpolant);

			copy.setAssertion(newFormula);
			copy.getSMTAnnotations().useSSA();

			copy.copyAllSuccessorsFromNode(node);

			m_nodeToCopy.put(node, copy);

			m_nodeToCopy_current.put(node, copy);
			m_copyToNode_current.put(copy, node);

			CFGExplicitNode original = m_copyToOriginal.get(node);
			if (original == null) // node is an original node
				original = node;
			m_copyToOriginal.put(copy, original);

			if (!copy.getAssertion().equals(m_script.term("true"))
					&& !copy.getAssertion().equals(m_script.term("false"))
					&& copy.getSMTAnnotations().getVars().isEmpty())
				assert false;
		}
	}

	/**
	 * delete last edge from copy to error location
	 * 
	 * @param cfgRoot
	 * @param error_trace
	 */
	private void deleteNewErrorEdge(CFGExplicitNode cfgRoot,
			ArrayList<IElement> error_trace) {

		CFGEdge toDelete = null;
		for (IEdge ce : ((CFGExplicitNode) error_trace
				.get(error_trace.size() - 1)).getIncomingEdges()) {
			if (ce.getSource() == m_nodeToCopy_current
					.get(((CFGExplicitNode) error_trace.get(error_trace.size() - 3))))
				toDelete = (CFGEdge) ce;
		}
		toDelete.deleteEdge();
	}

	/**
	 * redirect all edges which can be redirected by interpolant property
	 * without further theorem prover calls
	 * 
	 * @param error_trace
	 */
	private void redirectEdgesOnNewErrorPath(ArrayList<IElement> error_trace) {

		m_copied_error_trace = new ArrayList<IElement>();

		for (int i = 4; i < error_trace.size() - 1; i += 2) {
			CFGExplicitNode node = (CFGExplicitNode) error_trace.get(i);
			ArrayList<CFGEdge> toRemove = new ArrayList<CFGEdge>();

			CFGExplicitNode nodeOrig = m_copyToOriginal.get(node);

			for (Iterator<IEdge> it = node.getIncomingEdges().iterator(); it
					.hasNext();) {
				CFGEdge incoming_edge = (CFGEdge) it.next();// node.getIncomingEdges().get(j);

				// edge from initial node
				if (error_trace.get(2) == incoming_edge.getSource()) {
					CFGEdge hypoEdge = incoming_edge.copyWithoutNodes();
					hypoEdge.setSource(incoming_edge.getSource());
					hypoEdge.setTarget(m_nodeToCopy_current.get(node));

					m_copied_error_trace.add(hypoEdge.getSource());
					m_copied_error_trace.add(hypoEdge);

					s_logger.debug("redirecting edge" + incoming_edge
							+ " by interpolant property");
					toRemove.add(incoming_edge);
					break;
				}

				// always redirect edges which are parallel to the error trace
				// (when redirected),
				// additionally check whether there is another copied node which
				// comes before and
				// whose assertion is implied, too --> stronger refinement
				if (incoming_edge.getSource() == m_nodeToCopy_current
						.get(error_trace.get(i - 2))) {

					boolean nonDefault = false;

					boolean coverImpactStyle = false;// i.e. try redirecting of
														// backedges to all
														// nodes of the same
														// location
					if (coverImpactStyle) {

						for (int j = 4; j < i; j += 2) {
							CFGExplicitNode copy = m_nodeToCopy_current
									.get((CFGExplicitNode) error_trace.get(j));
							CFGExplicitNode copyOrig = m_copyToOriginal
									.get(copy);

							if (copyOrig.equals(nodeOrig)) {
								CFGEdge hypoEdge = incoming_edge
										.copyWithoutNodes();
								hypoEdge.setSource(incoming_edge.getSource());
								hypoEdge.setTarget(copy);

								LBool redirectEdge = hypoEdge.checkValidity();

								if (redirectEdge == LBool.UNSAT) {
									toRemove.add(incoming_edge);
									nonDefault = true;
									break;
								} else {
									hypoEdge.deleteEdge();
								}
							}
						}
					}
					if (!nonDefault) {
						// if nothing else works -- parallel to error trace
						CFGEdge hypoEdge = incoming_edge.copyWithoutNodes();
						hypoEdge.setSource(incoming_edge.getSource());
						hypoEdge.setTarget(m_nodeToCopy_current.get(node));

						m_copied_error_trace.add(hypoEdge.getSource());
						m_copied_error_trace.add(hypoEdge);

						s_logger.debug("redirecting edge" + incoming_edge
								+ " by interpolant property");

						toRemove.add(incoming_edge);
					}
				}
			}
			for (CFGEdge ed : toRemove) {
				ed.deleteEdge();
			}
		}
		m_copied_error_trace.add(m_nodeToCopy_current.get(error_trace
				.get(error_trace.size() - 2)));
	}

	/**
	 * check along the error trace if any incoming edges can be bent towards the
	 * copy of a node - do it in case
	 * 
	 * @param error_trace
	 * @param isPELtrace
	 */
	private void redirectEdges(ArrayList<IElement> error_trace,
			boolean isPELtrace) {
		for (Entry<CFGExplicitNode, CFGExplicitNode> e : m_nodeToCopy_current
				.entrySet()) {

			CFGExplicitNode node = e.getValue();
			ArrayList<CFGEdge> toRemove = new ArrayList<CFGEdge>();

			@SuppressWarnings("unchecked")
			ArrayList<CFGEdge> outgoingEdgesClone = (ArrayList<CFGEdge>) ((ArrayList<IEdge>) node
					.getOutgoingEdges()).clone();

			for (CFGEdge outgoing_edge : outgoingEdgesClone) {
				CFGExplicitNode currentCopy = m_nodeToCopy.get(outgoing_edge
						.getTarget());

				if (isPELtrace) {
					while (m_nodeToCopy.containsKey(currentCopy))
						currentCopy = m_nodeToCopy.get(currentCopy);
				}

				if (currentCopy != null) {
					CFGEdge hypoEdge = outgoing_edge.copyWithoutNodes();
					hypoEdge.setSource(node);
					hypoEdge.setTarget(currentCopy);

					LBool redirectEdge = hypoEdge.checkValidity();

					if (redirectEdge == LBool.UNSAT) {
						s_logger.debug("redirecting edge" + outgoing_edge);
						assert (hypoEdge.getTarget().getOutgoingEdges().size() > 0); // cf.
																						// cleanupGraph
																						// call
						toRemove.add(outgoing_edge);
						// break;
					} else {
						CFGExplicitNode loopStart = (CFGExplicitNode) hypoEdge
								.getTarget();
						hypoEdge.deleteEdge();

						boolean usePseudoELs = true;
						if (usePseudoELs) {
							CFGExplicitNode negatedLoopStart = loopStart
									.copyWithoutEdgesWithSSA();

							negatedLoopStart.getPayload().setName(
									"ERROR_Pseudo"
											+ negatedLoopStart.getPayload()
													.getName());
							negatedLoopStart.setAssertion(Util.not(m_script,
									negatedLoopStart.getAssertion()));

							CFGEdge additionalEdge = outgoing_edge
									.copyWithoutNodes();
							additionalEdge.setSource(outgoing_edge.getSource());
							additionalEdge.setTarget(negatedLoopStart);

							// zusaetzlich:
							if (checkPELEdges
									&& additionalEdge.checkValidity() == LBool.UNSAT)
								additionalEdge.deleteEdge();
						}
					}
				}
			}
			for (CFGEdge ed : toRemove) {
				ed.deleteEdge();
			}
		}

		this.m_performedChanges = true;
	}

	private void logStats(CFGExplicitNode cfgRoot) {
		s_logger.info("BMdata:(LAOnCFG) >(5)PC#: " + m_checkedPaths);
		s_logger.info("BMdata:(LAOnCFG) >(6)TIME#: " + m_totalTime);

		int edgeChecks = ((CFGEdge) cfgRoot.getOutgoingEdges().get(0))
				.getTheoremProverCount();
		long edgeChecksTime = ((CFGEdge) cfgRoot.getOutgoingEdges().get(0))
				.getTotalTime();

		s_logger.info("BMdata:(Edge Checks) >(7)EC#: " + edgeChecks);
		s_logger.info("BMdata:(Edge Checks) >(8)TIME#: " + edgeChecksTime);

		((CFGEdge) cfgRoot.getOutgoingEdges().get(0)).resetStats();
	}

	/*
	 * removes all unreachable nodes and edges from the graph
	 */
	private void cleanUpGraph(CFGExplicitNode cfgRoot) {
		// first step: collect all reachable nodes
		HashSet<CFGExplicitNode> reachableNodes = new HashSet<CFGExplicitNode>();
		collectReachable(cfgRoot, reachableNodes);

		// second step: collect all others
		HashSet<CFGExplicitNode> unreachableNodes = new HashSet<CFGExplicitNode>();
		HashSet<CFGExplicitNode> visited = new HashSet<CFGExplicitNode>();
		collectUnreachable(cfgRoot, reachableNodes, unreachableNodes, visited);

		ArrayList<CFGExplicitNode> unrAL = new ArrayList<CFGExplicitNode>();
		unrAL.addAll(unreachableNodes);

		// do not disconnect any nodes that may be redirected towards in the
		// future
		unrAL.removeAll(m_nodeToCopy.values());

		disconnectNodes(unrAL);
	}

	private void collectUnreachable(CFGExplicitNode node,
			HashSet<CFGExplicitNode> reachableNodes,
			HashSet<CFGExplicitNode> unreachableNodes,
			HashSet<CFGExplicitNode> visited) {

		visited.add(node);

		if (!reachableNodes.contains(node)) {
			unreachableNodes.add(node);
		}
		for (IEdge e : node.getOutgoingEdges()) {
			CFGExplicitNode targetNode = (CFGExplicitNode) (((CFGEdge) e)
					.getTarget());
			if (!visited.contains(targetNode))
				collectUnreachable(targetNode, reachableNodes,
						unreachableNodes, visited);
		}
		for (IEdge e : node.getIncomingEdges()) {
			CFGExplicitNode sourceNode = (CFGExplicitNode) (((CFGEdge) e)
					.getSource());
			if (!visited.contains(sourceNode)) {
				collectUnreachable(sourceNode, reachableNodes,
						unreachableNodes, visited);
			}
		}
	}

	private void collectReachable(CFGExplicitNode node,
			HashSet<CFGExplicitNode> reachableNodes) {
		reachableNodes.add(node);
		for (IEdge e : node.getOutgoingEdges()) {
			CFGExplicitNode targetNode = (CFGExplicitNode) (((CFGEdge) e)
					.getTarget());
			if (!reachableNodes.contains(targetNode))
				collectReachable(targetNode, reachableNodes);
		}
	}

	private void reportResult(IResult res) {
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_ID, res);
	}

	// -------------------------------------------------------------------------
	// ----------------------- search shortest Path ----------------------------
	// -------------------------------------------------------------------------

	// alternative search with BFS -> taken from SafetyChecker
	private ArrayList<IElement> searchShortestPath_BFS(
			CFGExplicitNode m_Graphroot) {
		ArrayList<IEdge> m_searchStack = new ArrayList<IEdge>();
		// m_searchStack.clear();
		for (IEdge e : m_Graphroot.getOutgoingEdges()) {
			m_searchStack.add(e);
			if (e.getTarget().getPayload().getName().contains("ERROR")) {
				return buildErrorPath(0, m_searchStack, m_Graphroot);
			}
		}

		int i = 0;
		// if the search stack still holds edges that might lead to an error
		// continue...
		while (i < m_searchStack.size()) {
			// get the current node which will be expanded
			INode node = m_searchStack.get(i).getTarget();
			// run through all descendants...
			for (IEdge e : node.getOutgoingEdges()) {
				INode target = e.getTarget();
				// check if descendant has already been visited by another
				// path(shorter path by construction of BFS)
				if (getNodeFromSearchStack(target, m_searchStack) < 0) {
					// append new edge to search stack since descendant has not
					// been visited yet
					m_searchStack.add(e);
					// check if descendant is an error node
					if (target.getPayload().getName().contains("ERROR")) {
						return buildErrorPath(m_searchStack.indexOf(e),
								m_searchStack, m_Graphroot);
						// return true;
					}
				}
			}
			i++;
		}
		return null;
	}

	// builds the error path by backtracking through search stack -> taken from
	// SafetyChecker
	private ArrayList<IElement> buildErrorPath(int errorIndex,
			ArrayList<IEdge> m_searchStack, CFGExplicitNode m_Graphroot) {
		ArrayList<IElement> m_ShortestPath = new ArrayList<IElement>();
		int i = errorIndex;
		while (i >= 0) {
			IEdge e = m_searchStack.get(i);
			m_ShortestPath.add(0, e.getTarget());
			m_ShortestPath.add(0, e);
			i = getNodeFromSearchStack(e.getSource(), m_searchStack);
		}
		m_ShortestPath.add(0, m_Graphroot);
		return m_ShortestPath;
	}

	// returns the index of the edge in the search stack that leads to the node
	// else returns -1
	// -> taken from SafetyChecker
	private int getNodeFromSearchStack(INode node,
			ArrayList<IEdge> m_searchStack) {
		for (IEdge e : m_searchStack) {
			if (e.getTarget() == node) {
				return m_searchStack.indexOf(e);
			}
		}
		return -1;
	}

	// -------------------------------------------------------------------------
	// ----------------------- interface stuff ----------------------------
	// -------------------------------------------------------------------------

	@Override
	public void finish() {
		// Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// Auto-generated method stub
		return null;
	}

	@Override
	public void init() {
		// Auto-generated method stub
	}

	@Override
	public boolean performedChanges() {
		return m_performedChanges;
	}

}
