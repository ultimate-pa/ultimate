package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.generalizers.Generalizer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulasAndLevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Literal;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.UnwindingNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.UnwindingProcRoot;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.ExceedsMaxTreeSizeException;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers.InterpolantsPathBlocker;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers.PreimagesPathBlocker;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers.TreeIC3BlockPathResult;

public class TreeIC3 {
	private UnwindingProcRoot artRoot;
	private Script script;
	private static Logger logger;
	private CFGExplicitNode cfgFunctionRoot;
	private HashMap<CFGExplicitNode, SortedMap<Integer, UnwindingNode>> artNodes;
	private HashSet<UnwindingNode> satErrorLocationNodes;
	private Set<CFGExplicitNode> loopLocations;
	private Generalizer generalizer;
	private boolean useHybrid;
	private int exceedingFactor = 5;
	// Plugin expects the following order:
	// BoogiePreprocessor, CFGBuilder, CFG2SMT, CFGReducer, ErrorLocationGenerator, IC3ModelChecker.
	
	
	public TreeIC3(CFGExplicitNode cfgFunctionRoot, Script script, Logger logger, Generalizer generalizer, boolean useHybrid) {
		this.script = script;
		TreeIC3.logger = logger;
		this.cfgFunctionRoot = cfgFunctionRoot;
		this.artNodes = new HashMap<CFGExplicitNode, SortedMap<Integer, UnwindingNode>>();
		this.satErrorLocationNodes = new HashSet<UnwindingNode>();
		this.generalizer = generalizer;
		this.useHybrid = useHybrid;
		this.artRoot = new UnwindingProcRoot(cfgFunctionRoot);
		HelperMethods.createEmptyClauseSet(artRoot);
		prepareArt(this.artRoot);
		// DEBUG:
		//Tests.smtParserTests(script, IC3ModelCheckerObserver.s_logger);
		Tests.equalityTests(script);
		Tests.nnfTransformerTests(script);
		Tests.dnfTransformerTests(script);
		Tests.nnfAndDnfTransformerTests(script);
		//Tests.approxPreimageTests(script);
		Tests.substitutionTests(script);
		//Tests.loopCfgNodesTests(cfgFunctionRoot);
		//Tests.createSimplifiedFormulaTests(script);
		Tests.termSizeCalculatorTests(script);
		Tests.freeVarsToConstTest(script);
	}
	
	
	
	/** Returns false if program is unsafe, else true if program is correct. */
	public boolean start() {
		TreeIC3.logger().debug("********************************************");
		TreeIC3.logger().debug("TreeIC3: Start.");
		TreeIC3.logger().debug("********************************************");
		// first store all loop locations from the CFG graph:
		this.loopLocations = HelperMethods.determineLoopLocations(cfgFunctionRoot);
		ArrayList<UnwindingNode> uncoveredArtLeaves = new ArrayList<UnwindingNode>();
		uncoveredArtLeaves.add(artRoot);
		
		while (!uncoveredArtLeaves.isEmpty()) {
			
//			try {
//				TreeIC3.logger().debug("");
//				TreeIC3.logger().debug("start(): DEBUG: Sleep one second.");
//				TreeIC3.logger().debug("");
//				Thread.sleep(1000);
//			} catch (InterruptedException e) {
//				e.printStackTrace();
//			}
			
			TreeIC3.logger().debug("Remaining uncovered leaves to handle: "+uncoveredArtLeaves.size());
			// unwind the ART:
			TreeIC3.logger().debug("Unwind one depth at all uncovered ART leaves...");
			artUnwinding(this.artRoot, uncoveredArtLeaves);
			if (uncoveredArtLeaves.isEmpty())
				TreeIC3.logger().debug("The ART could not be unwound further!");
			else {
				TreeIC3.logger().debug("ART has been unwound, freshly added ART leaves:");
				TreeIC3.logger().debug(HelperMethods.getListOfArtNodeNames(uncoveredArtLeaves));
				TreeIC3.logger().debug("");
			}
			TreeIC3.logger().debug("Now the ART looks like this:");
			TreeIC3.logger().debug(HelperMethods.artToString(artRoot));
			// DEBUG: Assert that ART is still inductive:
			assert(HelperMethods.isArtInductive(script, artRoot, satErrorLocationNodes));
			
			// path blocking:
			TreeIC3.logger().debug("");
			TreeIC3.logger().debug("Block all error paths...");
			boolean result = pathBlocking(uncoveredArtLeaves);
			if (result == false) {
				// We found a counterexample!
				TreeIC3.logger().info("TreeIC3: Program is incorrect!");
				return false;
			} else {
				TreeIC3.logger().debug("Blocking performed, there are no error paths.");
			}
			// strengthening:
			TreeIC3.logger().debug("");
			TreeIC3.logger().debug("Try to strengthen all new uncovered leaves...");
			if (uncoveredArtLeaves.size() == 0)
				TreeIC3.logger().debug("Problem: There are no new uncovered leaves!");
			boolean changed = true;
			while (changed) {
				ArrayList<UnwindingNode> backupUncoveredArtLeaves = new ArrayList<UnwindingNode>(uncoveredArtLeaves);
				ArrayList<UnwindingNode> workingList = new ArrayList<UnwindingNode>(uncoveredArtLeaves);
				while (!workingList.isEmpty()) {
					UnwindingNode uncoveredLeaf = workingList.remove(workingList.size()-1);
					// Take all art nodes with same location but smaller index and try to strengthen
					List<UnwindingNode> strengtheningPath = findPathToAncestorWithSameLocation(uncoveredLeaf);
					if (strengtheningPath == null) {
						TreeIC3.logger().debug("There is no other ART node by which this node could be strengthened.");
						continue;
					} else {
						TreeIC3.logger().info("Will apply strengthening by the following path:");
						TreeIC3.logger().info(HelperMethods.getListOfArtNodeNames(strengtheningPath));
						TreeIC3.logger().info("");
					}
					boolean didStrengthen = strengthening(strengtheningPath, uncoveredArtLeaves);
					TreeIC3.logger().debug("");
					if (didStrengthen) {
						TreeIC3.logger().info("Strengthened one path.");
					} else {
						TreeIC3.logger().info("Could not strengthen along this path.");
					}
					// node covering check
					TreeIC3.logger().info("Check if leaf is covered...");
					boolean didCover = nodeCovering(uncoveredLeaf, uncoveredArtLeaves);
					if (didCover) {
						TreeIC3.logger().info("Leaf has been covered.");
					}
				}
				changed = !backupUncoveredArtLeaves.equals(uncoveredArtLeaves);
			}
		}
		// All branches have been closed without finding a counterexample
		// -> program is correct
		TreeIC3.logger().info("TreeIC3: Program is correct!");
		return true;
	}
	
	
	
	/** Tries to block all satisfiable error paths. Returns false if it couldn't.*/
	private boolean pathBlocking(List<UnwindingNode> uncoveredArtLeaves) {
		while (true) {
			LinkedList<UnwindingNode> satErrorPath = findSatErrorPath();
			if (satErrorPath == null) return true;
			// TODO: Check if what we do here is correct
			TreeIC3BlockPathResult result = treeIC3BlockPath(satErrorPath);
			TreeIC3.logger().info("PathBlocking():");
			if (result.getCounterexample() != null) return false;
			// Transfer new clauses into the clause sets of the ART path
			ArrayList<Set<Clause>> trace = result.getTrace();
			FormulasAndLevelAnnotations edgeFormulasAndLvl = result.getEdgeFormulasAndLvl();
			Iterator<UnwindingNode> pathIterator = satErrorPath.iterator();
			assert(trace.size() == satErrorPath.size());
			int index = 0;
			while (pathIterator.hasNext()) {
				UnwindingNode node = pathIterator.next();
				Set<Clause> clauseSet = HelperMethods.getClauseSet(node);
				Term conjunction = Clause.buildConjunction(script, clauseSet).getFormula();
				
				boolean changed = false;
				for (Clause clause : trace.get(index)) {
					boolean added = addClauseIfNotImplied(clause, clauseSet, conjunction);
					if (added) {
						changed = true;
						TreeIC3.logger().info("Adding " +clause.toString()+" to "+
								node.getOriginalCFGNode().getPayload().getName());
						conjunction = Clause.buildConjunction(script, clauseSet).getFormula();
					}
				}
				if (changed)
					uncoverAllCoveredNodes(node, uncoveredArtLeaves);
				index++;
			}
			// TODO: My own modification:
			// If the path breaks at a certain node (becomes infeasible) after adding the clauses,
			// find all succeeding error nodes and remove them from SatErrorLocationNodes.
			// This is necessary because strengthening is only applied between nodes with same location
			// and thus unsatisfiable paths won't always get "false" at their last node. 
			int unsatIndex = existsUnsatPair(trace, edgeFormulasAndLvl);
			if (unsatIndex > -1) {
				removeErrorSubArtNodes(satErrorPath.get(unsatIndex));
			}
		}
	}
	
	/** Adds given clause to given clause set if it is not already implied by the
	 * formula defined by the clause set. Returns true if clause was added, else false. */
	private boolean addClauseIfNotImplied(Clause toAdd, Set<Clause> clauseSet, Term clauseSetFormula) {
		Term toCheck = script.term("=>",
				clauseSetFormula,
				toAdd.toTerm(script));
		LBool result2 = checkSat(script.term("not", toCheck));
		if (result2 == LBool.SAT) {
			// toCheck is not valid
			clauseSet.add(toAdd);
			return true;
		}
		return false;
	}
	
	
	/** If we found out that the given ART node has become unreachable, then we can remove all 
	 * error location nodes in its subtree from the satisfiable error location node list. 
	 * Note that this function just does the search and removal, it is not checked whether the given node
	 * is actually unreachable, the caller has to assert that himself. */
	private void removeErrorSubArtNodes(UnwindingNode artNode) {
		List<UnwindingNode> nodesWithSubtreesToSearch = new ArrayList<UnwindingNode>();
		nodesWithSubtreesToSearch.add(artNode);
		while (! nodesWithSubtreesToSearch.isEmpty()) {
			UnwindingNode currentNode = nodesWithSubtreesToSearch.remove(nodesWithSubtreesToSearch.size()-1);
			if (HelperMethods.hasErrorLocation(currentNode)) {
				satErrorLocationNodes.remove(currentNode);
			}
			if (currentNode.getOutgoingNodes() != null) {
				for (INode child : currentNode.getOutgoingNodes()) {
					nodesWithSubtreesToSearch.add((UnwindingNode) child);
				}
			}
		}
	}
	
	
	private static LinkedList<UnwindingNode> findPathToAncestorWithSameLocation(UnwindingNode startNode) {
		assert(startNode != null);
		CFGExplicitNode location = startNode.getOriginalCFGNode();
		assert(location != null);
		LinkedList<UnwindingNode> result = new LinkedList<UnwindingNode>();
		result.add(startNode);
		
		UnwindingNode currentNode = startNode;
		while(true) {
			currentNode = HelperMethods.getParentArtNode(currentNode);
			if (currentNode == null)
				return null;
			result.addFirst(currentNode);
			if (currentNode.getOriginalCFGNode() == location) {
				return result;				
			}
		}
	}
	

	
	/** Called by pathBlocking(), pure. 
	 * Tries to block the given error path and returns trace,
	 * or else returns a counterexample trace. <br/>
	 * Precondition: Last clause set must be satisfiable, or else we get an endless loop! */
	private TreeIC3BlockPathResult treeIC3BlockPath(List<UnwindingNode> satErrorPath) {
		if (useHybrid) {
			try {
				return new InterpolantsPathBlocker().treeIC3BlockPath(this, satErrorPath, exceedingFactor);
			} catch(ExceedsMaxTreeSizeException e) {
				logger.info("Falling back to PreimagesPathBlocker because interpolant conversion to CNF became to large.");
			}
		}
		return new PreimagesPathBlocker().treeIC3BlockPath(this, satErrorPath);
	}
	
	
	/** Reduces the given formula onto its non-primed variables. The formula should be of the form
	 * (and a b c'), whereas a is the formula of a node, b the formula of its outgoing edge and c' the 
	 * formula of the node it is leading to, primed accordingly to b. */
	public static Set<Cube> approxPreimage(FormulaAndLevelAnnotation formulaAndLvl, Script script) {
		TreeIC3.logger().debug("Calculating the preimage of");
		TreeIC3.logger().debug(formulaAndLvl);
		return ApproxPreimageCalculator.preimage(formulaAndLvl, script);
	}
	
	
	/** Tries to strengthen the last node in the path from the first one.
	 * Doesn't modify the nodes in between.
	 * Returns true if any clause has been propagated, else false. */
	private boolean strengthening(List<UnwindingNode> path, List<UnwindingNode> uncoveredArtLeaves) {
		script.push(1);
		assert(path.size() >= 2);
		UnwindingNode startNode = path.get(0);	// called v1 in article
		Set<Clause> phi = HelperMethods.getClauseSet(startNode);
		FormulaAndLevelAnnotation phiConjunctionAndLvl = Clause.buildConjunction(script, phi);
		UnwindingNode endNode = path.get(path.size()-1);	// called v2 in article
		Set<Clause> psi = HelperMethods.getClauseSet(endNode);
		FormulaAndLevelAnnotation psiConjunctionAndLvl = Clause.buildConjunction(script, psi);
		// TODO
		
		// determine phi_path:
		FormulasAndLevelAnnotations edgeFormulasAndLvl = HelperMethods.extractEdgeFormulasAndLvlFromArtPath(path);
		HashMap<BoogieVar, Integer> shiftLevelsAfterPath = new HashMap<BoogieVar, Integer>(); 
		Term phi_path = HelperMethods.concatenateEdgeFormulas(shiftLevelsAfterPath, edgeFormulasAndLvl, script);
		TreeIC3.logger().debug("Concatenated path for strengthening:");
		TreeIC3.logger().debug(phi_path.toStringDirect());
		
		// collect all clauses that we can propagate in bigC:
		Set<Clause> bigC = new HashSet<Clause>();
		for(Clause clause : phi) {
			FormulaAndLevelAnnotation clauseFormulaAndLvl = clause.toFormulaAndLvl(script);
			Term clauseFormula = clauseFormulaAndLvl.getFormula();
			Term firstImplication = script.term("not", script.term("=>",
									psiConjunctionAndLvl.getFormula(),
									clauseFormula));
			LBool firstResult = checkSat(firstImplication);
			
			// Determine how the clause would look like after the path (concerning shifting variables)
			FormulaAndLevelAnnotation primedClauseAndLvlAtLastNode =
					SubstitutionManager.substituteSpecificInToOut(script, clauseFormulaAndLvl,
							shiftLevelsAfterPath, false);
			Term secondImplication = script.term("not", script.term("=>", 
					script.term("and", phiConjunctionAndLvl.getFormula(), phi_path),
					primedClauseAndLvlAtLastNode.getFormula()));
			LBool secondResult = checkSat(secondImplication);
			
			if (firstResult == LBool.SAT && secondResult == LBool.UNSAT) {
				bigC.add(clause);
			}
		}
		script.pop(1);

		if (!bigC.isEmpty()) {
			// Refute not(bigC):
			// Temporarily add not(bigC) to last node of path and call treeIC3BlockPath().
			// Problem: We can only add clauses to the last node's clause set.
			// But regarding how treeIC3BlockPath works, we can also add a fake clause
			TreeIC3.logger().debug("We can propagate these clauses (bigC):");
			TreeIC3.logger().debug(bigC);
			TreeIC3.logger().debug("Will now temporarily add not(bigC) to last node and call treeIC3BlockPath().");
			
			Set<Clause> lastNodeClauseSet = HelperMethods.getClauseSet(path.get(path.size()-1));
			
			FormulaAndLevelAnnotation bigCFormulaAndLvl = Clause.buildConjunction(script, bigC);
			Term notBigCFormula = script.term("not", bigCFormulaAndLvl.getFormula());
			FormulaAndLevelAnnotation notBigCFormulaAndLvl = new FormulaAndLevelAnnotation(notBigCFormula,
																		bigCFormulaAndLvl.getLevelAnnotation());
			Literal notBigCFakeLiteral = new Literal(true, notBigCFormulaAndLvl);
			Clause notBigC = new Clause(notBigCFakeLiteral);
			
			lastNodeClauseSet.add(notBigC);
			TreeIC3BlockPathResult result = treeIC3BlockPath(path);
			boolean removedNotBigC = lastNodeClauseSet.remove(notBigC);
			assert(removedNotBigC);
			
			ArrayList<Set<Clause>> trace = result.getTrace();
			assert(trace != null);
			Iterator<UnwindingNode> iterator = path.iterator();
			int index = 0;
			assert(trace.size() == path.size());
			// go along path and trace and add all clauses from trace to path
			// EXCEPT for the last one where we added notBigC, there we will
			// add bigC instead
			while (iterator.hasNext()) {
				UnwindingNode node = iterator.next();
				Set<Clause> clauseSet = HelperMethods.getClauseSet(node);
				Term conjunction = Clause.buildConjunction(script, clauseSet).getFormula();
				Set<Clause> clausesToAdd = trace.get(index);
				if (!iterator.hasNext())
					clausesToAdd = bigC;
				else
					clausesToAdd = trace.get(index);
				boolean changed = false;
				for (Clause clause : clausesToAdd) {
					boolean added = addClauseIfNotImplied(clause, clauseSet, conjunction);
					if (added) {
						TreeIC3.logger().info("Added "+clause+" to "+node.getOriginalCFGNode().getPayload().getName());
						conjunction = Clause.buildConjunction(script, clauseSet).getFormula();
						changed = true;
					}
				}
				if (changed)
					uncoverAllCoveredNodes(node, uncoveredArtLeaves);
				index++;
			}
			return true;
		} else {
			return false;
		}
	}
	
	
	
	/** Returns the node index if there exists a pair of a node and its outgoing edge such that 
	 * nodeClauseSet && edgeFormula is unsatisfiable, or -1 if it doesn't exist. There's one exception
	 * that the last triple of prelast nodeClauseSet && edgeFormula && last nodeClauseSet is checked together
	 * for unsatisfiability. */
	public int existsUnsatPair(ArrayList<Set<Clause>> nodeClauses, FormulasAndLevelAnnotations edgeFormulasAndLvl) {
		ArrayList<Term> edgeFormulas = edgeFormulasAndLvl.getEdgeFormulas();
		ArrayList<LevelAnnotations> edgeLvlAnnotations = edgeFormulasAndLvl.getLevelAnnotations();
		assert(nodeClauses.size()-1 == edgeFormulas.size());
		
		for (int i = 0; i < nodeClauses.size()-1; i++) {
			Set<Clause> nodeClauseSet = nodeClauses.get(i);
			Term edgeFormula = edgeFormulas.get(i);

			// check if unsatisfiable
			// constant substitution
			FormulaAndLevelAnnotation conjunctionAndLvl = Clause.buildConjunction(script, nodeClauseSet);
			Term toCheck;
			if (i == nodeClauses.size()-2) {
				// last case, check triple instead
				FormulaAndLevelAnnotation lastConjunctionAndLvl = Clause.buildConjunction(script,
																		nodeClauses.get(i+1));
				LevelAnnotations edgeLvl = edgeLvlAnnotations.get(i);
				FormulaAndLevelAnnotation lastConjunctionPrimedAndLvl = 
						HelperMethods.shiftFormulaByEdge(script, lastConjunctionAndLvl, edgeLvl);
				toCheck = script.term("and", conjunctionAndLvl.getFormula(),
						edgeFormula, lastConjunctionPrimedAndLvl.getFormula());
			} else {
				// not the last case, do as written in original paper
				toCheck = script.term("and", conjunctionAndLvl.getFormula(),
						edgeFormula);	
			}
			
			TreeIC3.logger().debug("existsUnsatPair(): Check if "+toCheck.toStringDirect()+" is unsatisfiable");
			LBool result = TreeIC3.checkSat(script, toCheck);
			
			if (result == LBool.UNSAT) {
				TreeIC3.logger().debug("It is unsat.");
				return i;
			} else {
				TreeIC3.logger().debug("It is sat.");
			}
		}
		// could not detect an unsatisfiability
		TreeIC3.logger().debug("All pairs are sat.");
		return -1;
	}

	
	
	/** Returns any error path beginning from the root ART node, or null if there is none. */ 
	private LinkedList<UnwindingNode> findSatErrorPath() {
		if (satErrorLocationNodes.isEmpty()) return null;
		LinkedList<UnwindingNode> result = new LinkedList<UnwindingNode>();
		UnwindingNode currentNode = satErrorLocationNodes.iterator().next();
		do {
			result.addFirst(currentNode);
			currentNode = HelperMethods.getParentArtNode(currentNode);
		} while (currentNode != null);
		return result;
	}
	
	
	private void prepareArt(UnwindingProcRoot artRoot) {
		HelperMethods.setIC3Index(artRoot, 1);
		registerArtNode(artRoot, false);
	}
	
	
	/** Unwinds the ART one step at every uncovered leaf. The content of given uncoveredArtLeaves is
	 * cleared and replaced by the new uncovered ART leaves. */
	private void artUnwinding(UnwindingProcRoot artRoot, List<UnwindingNode> uncoveredArtLeaves) {
		List<UnwindingNode> newUncoveredArtLeaves = new ArrayList<UnwindingNode>();
		
		for (UnwindingNode uncoveredArtLeaf : uncoveredArtLeaves) {
			// pop leaf from uncovered leaves
			int uncoveredArtLeafIndex = HelperMethods.getIC3Index(uncoveredArtLeaf);
			CFGExplicitNode location = uncoveredArtLeaf.getOriginalCFGNode();
			
			if (location.getOutgoingEdges().size() == 0)
				TreeIC3.logger().debug("artUnwinding(): The location " + location.getPayload().getName()
						+ " doesn't have any successor nodes.");
				// Note that this doesn't have to be an error
			for(IEdge iedge : location.getOutgoingEdges()) {
				// create ART edge and child node and connect them to uncoveredArtLeaf
				CFGEdge cfgEdge = (CFGEdge) iedge;
				CFGEdge newEdge = cfgEdge.copyWithoutNodesUsingSSAMapping(
									     uncoveredArtLeaf.getSMTAnnotations().getSSAMapping());
				// We have to apply two modifications here:
				// 1. Sometimes there are assertions in the target node of an edge -> move these into the edge
				// 2. We want to rename inVars and outVars, f.ex. inVar v_x_3 -> xIn
				Object[] edgeAndNodeSmt = HelperMethods.extractEdgeAndNodeSmtForCfgEdge(cfgEdge);
				SMTEdgeAnnotations edgeSmt = (SMTEdgeAnnotations) edgeAndNodeSmt[0];
				SMTNodeAnnotations nodeSmt = null;
				if (edgeAndNodeSmt.length > 1)
					nodeSmt = (SMTNodeAnnotations) edgeAndNodeSmt[1];
				FormulaAndLevelAnnotation edgeFormulaAndLvl = new FormulaAndLevelAnnotation(edgeSmt.getAssumption(),
															new LevelAnnotations(edgeSmt, null));
				FormulaAndLevelAnnotation nodeFormulaAndLvl;
				if (nodeSmt != null)
					nodeFormulaAndLvl = new FormulaAndLevelAnnotation(nodeSmt.getAssertion(),
																	new LevelAnnotations(null, nodeSmt));
				else
					nodeFormulaAndLvl = null;
				FormulaAndLevelAnnotation substEdgeFormulaAndLvl = HelperMethods.createSimplifiedFormula(
					script, edgeFormulaAndLvl, nodeFormulaAndLvl);
				// write lvl edge annotation to art edge
				HelperMethods.setFormulaAndLvlForArtEdge(newEdge, substEdgeFormulaAndLvl);
				
				TreeIC3.logger().debug("We placed this simplified formula on the edge:");
				TreeIC3.logger().debug(HelperMethods.getFormulaAndLvlFromArtEdge(newEdge));
				newEdge.setSource(uncoveredArtLeaf);
				UnwindingNode child = new UnwindingNode((CFGExplicitNode) iedge.getTarget(),
														true, artRoot);
				HelperMethods.createEmptyClauseSet(child);
				newEdge.setTarget(child);
				assert(HelperMethods.getFormulaFromArtEdge(newEdge).equals(substEdgeFormulaAndLvl.getFormula()));
				// These assertions should be fulfilled by newEdge.setSource and newEdge.setTarget:
				assert(child.getIncomingNodes().contains(uncoveredArtLeaf));
				assert(uncoveredArtLeaf.getOutgoingNodes().contains(child));
				assert(child.getIncomingEdges().contains(newEdge));
				assert(uncoveredArtLeaf.getOutgoingEdges().contains(newEdge));
				// set index of child
				HelperMethods.setIC3Index(child, uncoveredArtLeafIndex+1);
				registerArtNode(child, true);
				// push child onto newly uncovered leaves
				newUncoveredArtLeaves.add(child);
			}
		}
		// These new leaves all hold the formula "true".
		uncoveredArtLeaves.clear();
		uncoveredArtLeaves.addAll(newUncoveredArtLeaves);
	}
	
	
	/** Checks if given node is covered by another node with smaller index and same location
	 * (not necessarily predecessor in ART) and possibly covers it. Doesn't unwind the ART.<br/> 
	 * Returns true if the given node could be covered, else false.*/
	private boolean nodeCovering(UnwindingNode leaf, List<UnwindingNode> uncoveredArtLeaves) {
		// check if the leaf is covered by a predecessor
		// TODO
		if (leaf.isCovered()) {
			return false;
		}
		Collection<UnwindingNode> preNodes = getNodesWithSameLocationButSmallerIndex(leaf);
		if (preNodes == null) return false;
		FormulaAndLevelAnnotation nodeFormulaAndLvl = 
				Clause.buildConjunction(script, HelperMethods.getClauseSet(leaf));
		Iterator<UnwindingNode> iterator = preNodes.iterator();
		while (iterator.hasNext()) {
			UnwindingNode preNode = iterator.next();
			FormulaAndLevelAnnotation preNodeFormulaAndLvl = 
					Clause.buildConjunction(script, HelperMethods.getClauseSet(preNode));
			
			TreeIC3.logger().debug("Checking if "+preNodeFormulaAndLvl+" covers / is implied by "+nodeFormulaAndLvl);
			// check if node.formula implies preNode.formula, then we can cover it
			Term toCheck = script.term("not", script.term("=>", nodeFormulaAndLvl.getFormula(), preNodeFormulaAndLvl.getFormula()));
			LBool result = checkSat(toCheck);
						
			if (result == LBool.UNSAT) {
				// mark node as covered by preNode
				coverNode(preNode, leaf, uncoveredArtLeaves);
				// uncover all other nodes covered by node
				uncoverAllCoveredNodes(leaf, uncoveredArtLeaves);
				return true;
			}
		}
		return false;
	}
	
	
	/** Registers given ART node such that it can be found easily by program location
	 * (underlying CFG node) and ic3 index. Will also be added to errorLocationNodes if
	 * corresponding CFG node is an error location.<br/>
	 * You should call this on every node you add to the ART. */
	private void registerArtNode(UnwindingNode artNode, boolean knowThatSatisfiable) {
		if (HelperMethods.hasErrorLocation(artNode) && (knowThatSatisfiable || isSatisfiableNode(artNode)))
			satErrorLocationNodes.add(artNode);
		SortedMap<Integer, UnwindingNode> map = artNodes.get(artNode.getOriginalCFGNode());
		if (map == null) {
			map = new TreeMap<Integer, UnwindingNode>();
			artNodes.put(artNode.getOriginalCFGNode(), map);
		}
		map.put(HelperMethods.getIC3Index(artNode), artNode);
	}
	
	/** Checks if the annotated formula of this ART node is satisfiable */
	private boolean isSatisfiableNode(UnwindingNode artNode) {
		Set<Clause> clauseSet = HelperMethods.getClauseSet(artNode);
		FormulaAndLevelAnnotation conjunction = Clause.buildConjunction(script, clauseSet);
		Term toCheck = conjunction.getFormula();
		LBool result = checkSat(toCheck);
		if (result == LBool.SAT) return true;
		if (result == LBool.UNKNOWN)
			throw new RuntimeException("isSatisfiableNode(): Could not determine satisfiability!");
		return false;
	}
	
	/** Unregisters given ART node and removes it from errorLocationNodes if it represented
	 * an error location. You should call this on every node you remove from the ART. */
	private void unregisterArtNode(UnwindingNode artNode) {
		if (HelperMethods.hasErrorLocation(artNode))
			satErrorLocationNodes.remove(artNode);
		SortedMap<Integer, UnwindingNode> map = artNodes.get(artNode.getOriginalCFGNode());
		assert(map != null);
		map.remove(artNode.getOriginalCFGNode());
		if (map.isEmpty())
			artNodes.remove(artNode.getOriginalCFGNode());
	}
	
	/** Returns a collection of nodes with same location, but smaller index as the given node,
	 * sorted ascendingly by the index. */
	private Collection<UnwindingNode> getNodesWithSameLocationButSmallerIndex(UnwindingNode node) {
		CFGExplicitNode location = node.getOriginalCFGNode();
		Integer index = HelperMethods.getIC3Index(node);
		SortedMap<Integer, UnwindingNode> map = artNodes.get(location);
		if (map == null) return null;
		SortedMap<Integer, UnwindingNode> smallerIndexMap = map.headMap(index);
		Collection<UnwindingNode> result = smallerIndexMap.values();
		if (result.size() == 0) return null;
		return result;
	}
	
	private static void coverNode(UnwindingNode coveringNode, UnwindingNode coveredNode, List<UnwindingNode> uncoveredArtLeaves) {
		coveringNode.get_coveredNodes().add(coveredNode);
		coveredNode.setCovered(true);
		coveredNode.set_coveringNode(coveringNode);
		uncoveredArtLeaves.removeAll(getSubTreeLeaves(coveredNode));
		// covered nodes are not removed from the ART, so no unregisterArtNode() is needed,
		// but it may be that once they are uncovered later, no unwinding will be needed
		// anymore
	}
	
	private static void uncoverNode(UnwindingNode coveredNode, List<UnwindingNode> uncoveredArtLeaves) {
		UnwindingNode coveringNode = coveredNode.get_coveringNode();
		coveringNode.get_coveredNodes().remove(coveredNode);
		coveredNode.setCovered(false);
		coveredNode.set_coveringNode(null);
		uncoveredArtLeaves.addAll(getSubTreeLeaves(coveredNode));
	}
	
	private static void uncoverAllCoveredNodes(UnwindingNode coveringNode, List<UnwindingNode> uncoveredArtLeaves) {
		ArrayList<UnwindingNode> coveredNodes = coveringNode.get_coveredNodes();
		if (coveredNodes == null)
			return;
		while (!coveredNodes.isEmpty()) {
			UnwindingNode coveredNode = coveredNodes.remove(coveredNodes.size()-1);
			uncoverNode(coveredNode, uncoveredArtLeaves);
		}
	}
	
	private static List<UnwindingNode> getSubTreeLeaves(UnwindingNode artNode) {
		// TODO: Check if this is really necessary. Perhaps (un-)covering nodes only
		// happens to leaves? Then it would be senseless to search for further subtree leaves.
		List<UnwindingNode> exploring = new ArrayList<UnwindingNode>();
		List<UnwindingNode> result = new ArrayList<UnwindingNode>();
		exploring.add(artNode);
		while (!exploring.isEmpty()) {
			UnwindingNode currentNode = exploring.remove(exploring.size()-1);
			if (isLeaf(currentNode))
				result.add(currentNode);
			else
				exploring.addAll((Collection<? extends UnwindingNode>) currentNode.getOutgoingNodes());
		}
		return result;
	}
	
	/** Remark: Does not pay attention if given node is covered. */
	private static boolean isLeaf(UnwindingNode artLeaf) {
		if (artLeaf.getOutgoingEdges() != null && artLeaf.getOutgoingEdges().size() > 0) {
			assert(artLeaf.getOutgoingNodes().size() > 0);
			return false;
		} else {
			assert(artLeaf.getOutgoingNodes() == null || artLeaf.getOutgoingNodes().size() == 0);
			return true;
		}
	}
	
	private LBool checkSat(Term toCheck) {
		return checkSat(script, toCheck);
	}
	public static LBool checkSat(Script script, Term toCheck) {
		script.push(1);
		ConstSubstResult constSubstResult = SubstitutionManager.substituteFreeVarsToConst(script, toCheck, null); 
		Term toCheck2 = constSubstResult.getSubstTerm(); 
		script.assertTerm(toCheck2);
		LBool result = script.checkSat();
		script.pop(1);
		return result;
	}
	
	public UnwindingProcRoot getArtRoot() {
		return this.artRoot;
	}
	
	public Script getScript() {
		return this.script;
	}
	
	public Generalizer getGeneralizer() {
		return this.generalizer;
	}
	
	public static Logger logger() {
		return logger;
	}
}
