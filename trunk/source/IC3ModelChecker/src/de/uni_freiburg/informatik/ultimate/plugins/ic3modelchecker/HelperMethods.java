package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulasAndLevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.IC3Annotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.UnwindingNode;

public class HelperMethods {


	
	public static void createEmptyClauseSet(UnwindingNode node) {
		Set<Clause> emptyClauseSet = new HashSet<Clause>();
		IC3Annotation ic3annotation = new IC3Annotation();
		ic3annotation.setClauseSet(emptyClauseSet);
		assert(node.getPayload().getAnnotations().containsKey("ic3annotation") == false);
		node.getPayload().getAnnotations().put("ic3annotation", ic3annotation);
	}

	public static Set<Clause> getClauseSet(UnwindingNode node) {
		IC3Annotation ic3annotation = (IC3Annotation) node.getPayload().getAnnotations().get("ic3annotation");
		assert (ic3annotation != null);
		return ic3annotation.getClauseSet();
	}

	public static void setClauseSet(UnwindingNode node, Set<Clause> clauseSet) {
		IC3Annotation ic3annotation = (IC3Annotation) node.getPayload().getAnnotations().get("ic3annotation");
		if (ic3annotation == null) {
			ic3annotation = new IC3Annotation();
			node.getPayload().getAnnotations().put("ic3annotation", ic3annotation);
		}
		ic3annotation.setClauseSet(clauseSet);
	}

	public static int getIC3Index(UnwindingNode node) {
		IC3Annotation ic3annotation = (IC3Annotation) node.getPayload().getAnnotations().get("ic3annotation");
		assert (ic3annotation != null);
		return ic3annotation.getIndex();
	}

	public static void setIC3Index(UnwindingNode node, int index) {
		IC3Annotation ic3annotation = (IC3Annotation) node.getPayload().getAnnotations().get("ic3annotation");
		if (ic3annotation == null) {
			ic3annotation = new IC3Annotation();
			node.getPayload().getAnnotations().put("ic3annotation", ic3annotation);
		}
		ic3annotation.setIndex(index);
	}

	public static HashMap<Term, Term> mirrorMap(HashMap<Term, Term> substMap) {
		HashMap<Term, Term> result = new HashMap<Term, Term>();
		Set<Entry<Term, Term>> entrySet = substMap.entrySet();
		for (Entry<Term, Term> entry : entrySet) {
			assert(!result.containsKey(entry.getValue()));
			result.put(entry.getValue(), entry.getKey());
		}
		return result;
	}
	
	/** Returns a formula in which all term vars are properly renamed to Boogie varname + level. */
	public static FormulaAndLevelAnnotation createSimplifiedFormula(Script script, FormulaAndLevelAnnotation edgeFormulaAndLvl,
																  FormulaAndLevelAnnotation nodeFormulaAndLvl) {
		FormulaAndLevelAnnotation edgeSubst = SubstitutionManager.substituteInOut(script, edgeFormulaAndLvl);

		if (nodeFormulaAndLvl == null) {
			TreeIC3.logger().debug(edgeFormulaAndLvl+" been transformed into "+edgeSubst);
			return edgeSubst;
		}
		// Else we also have a non-trivial node formula which has to be prepared and added:
		HashMap<BoogieVar, Integer> shiftLevelPerVariable = new HashMap<BoogieVar, Integer>();
		determineShiftLevelsFromEdge(shiftLevelPerVariable , edgeSubst.getLevelAnnotation(), 1);
		FormulaAndLevelAnnotation nodeSubst = SubstitutionManager.substituteSpecificInToOut(script, nodeFormulaAndLvl,
																							   shiftLevelPerVariable, true);
		Term formula = script.term("and", edgeSubst.getFormula(), nodeSubst.getFormula());
		List<LevelAnnotations> lvlList = new ArrayList<LevelAnnotations>();
		lvlList.add(edgeSubst.getLevelAnnotation());
		lvlList.add(nodeSubst.getLevelAnnotation());
		LevelAnnotations mergedLvl = LevelAnnotations.getMerged(lvlList, null);
		FormulaAndLevelAnnotation result = new FormulaAndLevelAnnotation(formula, mergedLvl);
		TreeIC3.logger().debug(edgeFormulaAndLvl+" together with "+nodeFormulaAndLvl+" been transformed into "+result);
		return result;
	}
	
	/** Returns all edge formulas together with their level annotations from given path through the ART. */
	public static FormulasAndLevelAnnotations extractEdgeFormulasAndLvlFromArtPath(List<UnwindingNode> path) {
		assert(path.size() >= 2);
		Iterator<UnwindingNode> nodeIterator = path.iterator();
		// the first node doesn't have an ingoing edge, discard it
		nodeIterator.next();
		// save the path's edge formulas into edgeFormulas
		ArrayList<Term> edgeFormulas = new ArrayList<Term>();
		// save the path's edge lvl annotations into lvlAnnotations
		ArrayList<LevelAnnotations> lvlAnnotations = new ArrayList<LevelAnnotations>();
		while (nodeIterator.hasNext()) {
			UnwindingNode node = nodeIterator.next();
			// we can determine the path edge as the ingoing edge of
			// the current node
			List<IEdge> incomingEdges = node.getIncomingEdges();
			assert(incomingEdges.size() == 1);
			CFGEdge edge = (CFGEdge) incomingEdges.get(0);
			SMTEdgeAnnotations smtEdgeAnnotation = edge.getSMTAnnotations();
			// now get the edge formula:
			Term edgeFormula = HelperMethods.getFormulaFromArtEdge(edge);
			edgeFormulas.add(edgeFormula);
			lvlAnnotations.add(new LevelAnnotations(smtEdgeAnnotation, null));
		}
		assert(edgeFormulas.size() + 1 == path.size());
		return new FormulasAndLevelAnnotations(edgeFormulas, lvlAnnotations);
	}
	
	/** Returns Object[1] containing the smt annotations of given cfg edge if only the edge carries smt. <br/>
	 * If also the cfg node where that edge is leading to contains smt, returns Object[2], where the 
	 * edge smt is in result[0] and the node smt is in result[1]. <br/>
	 * Pure. */
	public static Object[] extractEdgeAndNodeSmtForCfgEdge(CFGEdge cfgEdge) {
		CFGExplicitNode targetNode = (CFGExplicitNode) cfgEdge.getTarget();
		assert(targetNode != null);
		SMTEdgeAnnotations edgeAnnotation = ((SMTEdgeAnnotations) cfgEdge.getPayload().
				getAnnotations().get("SMT")).clone();
		SMTNodeAnnotations nodeAnnotation = (SMTNodeAnnotations) targetNode.getPayload().
				getAnnotations().get("SMT");
		assert(edgeAnnotation != null);
		if (nodeAnnotation != null) {
			Term nodeAssertion = nodeAnnotation.getAssertion();
			Script script = nodeAnnotation.getScript();
			assert(script != null);
			if (nodeAssertion != null && !nodeAssertion.equals(script.term("true"))) {
				return new Object[] {edgeAnnotation, nodeAnnotation};
			}
		}
		return new Object[] {edgeAnnotation};
	}
	
	public static boolean hasErrorLocation(UnwindingNode artNode) {
		return (artNode.getOriginalCFGNode().getPayload().getName().startsWith("ERROR"));
	}
	
	/** Note: ART edges are of type CFGEdge (quite confusing) */
	public static Term getFormulaFromArtEdge(CFGEdge artEdge) {
		SMTEdgeAnnotations annotation = (SMTEdgeAnnotations) artEdge.getPayload().
				getAnnotations().get("SMT");
		return annotation.getAssumption();
	}
	
	public static FormulaAndLevelAnnotation getFormulaAndLvlFromArtEdge(CFGEdge artEdge) {
		SMTEdgeAnnotations smtEdgeAnnotation = (SMTEdgeAnnotations) artEdge.getPayload().
				getAnnotations().get("SMT");
		Term formula = smtEdgeAnnotation.getAssumption();
		LevelAnnotations lvlAnnotation = new LevelAnnotations(smtEdgeAnnotation, null);
		return new FormulaAndLevelAnnotation(formula, lvlAnnotation);
	}
	
	public static void setFormulaAndLvlForArtEdge(CFGEdge artEdge, FormulaAndLevelAnnotation formulaAndLvl) {
		SMTEdgeAnnotations smtEdgeAnnotation = formulaAndLvl.getLevelAnnotation().extractToSmtEdgeAnnotations();
		smtEdgeAnnotation.setAssumption(formulaAndLvl.getFormula());
		artEdge.getPayload().getAnnotations().put("SMT", smtEdgeAnnotation);
	}
	
	
	public static UnwindingNode getParentArtNode(UnwindingNode child) {
		List<INode> incomingNodes = child.getIncomingNodes();
		if (incomingNodes != null && incomingNodes.size() > 1) {
			throw new RuntimeException("ERROR in getParentArtNode(): IncomingNodes.size() > 1");
		}
		else if (incomingNodes == null || incomingNodes.size() == 0) {
			return null;
		}
		else {
			return (UnwindingNode) incomingNodes.get(0);	
		}
	}
	
	
	
	public static ArrayList<Set<Clause>> extractClauseSetsFromPath(List<UnwindingNode> path, boolean copyClauseSet) {
		assert(path.size() >= 2);
		ArrayList<Set<Clause>> trace = new ArrayList<Set<Clause>>();
		Iterator<UnwindingNode> nodeIterator = path.iterator();
		// save the node clauses into the trace
		while (nodeIterator.hasNext()) {
			UnwindingNode node = nodeIterator.next();
			Set<Clause> clauseSet = HelperMethods.getClauseSet(node);
			if (copyClauseSet)
				trace.add(new HashSet<Clause>(clauseSet));
			else
				trace.add(clauseSet);
		}
		return trace;
	}
	
	/** Modifies shiftLevelPerVariable. Concatenates all given edge formulas, priming the variables accordingly.<br/>
	 * Example: xL1 = xL0 + 1; xL0 > 2; ==> xL1 = xL0 + 1 and xL1 > 2 <br/>
	 * But: xL0 = 1 and yL1 = yL0 - 1; xL0 > 0; ==> xL0 = 1 and yL1 = yL0 - 1 and xL0 > 0*/
	public static Term concatenateEdgeFormulas(HashMap<BoogieVar, Integer> shiftLevelPerVariable, FormulasAndLevelAnnotations edgeFormulasAndLvl, Script script) {
		ConcatenationResult concatenationResult = getConcatenation(shiftLevelPerVariable, edgeFormulasAndLvl, script);
		Term[] adaptedTerms = new Term[concatenationResult.formulasAndLvl.size()];
		concatenationResult.formulasAndLvl.getEdgeFormulas().toArray(adaptedTerms);
		assert(edgeFormulasAndLvl.size() == adaptedTerms.length);
		if (adaptedTerms.length > 1)
			return script.term("and", adaptedTerms);
		else
			return adaptedTerms[0];
	}
	
	/** Modifies shiftLevelPerVariable. Simulates a concatenation of given edge formulas and returns how they would be primed,
	 * as well as the shift levels that would be used to prime them (see SubstitutionManager.substituteSpecificInToOut()).
	 * The shift levels at index i indicate the shifting spanning over the first i edge formulas. */
	public static ConcatenationResult getConcatenation(HashMap<BoogieVar, Integer> shiftLevelPerVariable, FormulasAndLevelAnnotations edgeFormulasAndLvl, Script script) {
		ArrayList<Term> edgeFormulas = edgeFormulasAndLvl.getEdgeFormulas();
		ArrayList<LevelAnnotations> lvlAnnotations = edgeFormulasAndLvl.getLevelAnnotations();
		TreeIC3.logger().debug("Applying getConcatenation() on following edge formulas:");
		TreeIC3.logger().debug(edgeFormulasAndLvl.toString());
		
		ArrayList<FormulaAndLevelAnnotation> shiftedFormulasAndLvl = new ArrayList<FormulaAndLevelAnnotation>();
		ArrayList<HashMap<BoogieVar, Integer>> shiftLevelsForPath = new ArrayList<HashMap<BoogieVar, Integer>>();
		shiftLevelsForPath.add(new HashMap<BoogieVar, Integer>(shiftLevelPerVariable));
		Iterator<Term> formulaIterator = edgeFormulas.iterator();
		Iterator<LevelAnnotations> lvlIterator = lvlAnnotations.iterator();
		while (formulaIterator.hasNext()) {
			Term edgeFormula = formulaIterator.next();
			LevelAnnotations lvlAnnotation = lvlIterator.next();

			FormulaAndLevelAnnotation formulaAndLvl = SubstitutionManager.substituteSpecificInToOut(script,
						new FormulaAndLevelAnnotation(edgeFormula, lvlAnnotation), shiftLevelPerVariable, false);
			
			shiftedFormulasAndLvl.add(formulaAndLvl);

			// determine for next loop execution which variables have been modified:
			determineShiftLevelsFromEdge(shiftLevelPerVariable, lvlAnnotation, 1);
			shiftLevelsForPath.add(new HashMap<BoogieVar, Integer>(shiftLevelPerVariable));
		}
		assert(shiftLevelsForPath.size() == shiftedFormulasAndLvl.size() + 1);
		return new ConcatenationResult(new FormulasAndLevelAnnotations(shiftedFormulasAndLvl), shiftLevelsForPath);
	}
	
	/** Determines from given path level annotations which variables are changed and
	 * returns shift levels which can then be used for SubstitutionManager.substituteSpecificInToOut().<br/>
	 * A shift level at index i (counting from 0) always spans over the first i level annotations.
	 * Thus, it holds that for all BoogieVars x result[j][x] <= result[j+1][x].*/
	public static ArrayList<HashMap<BoogieVar, Integer>> determineShiftLevelsFromPath(
			List<LevelAnnotations> pathLvl, int startLevelOnFirstModification) {
		HashMap<BoogieVar, Integer> shiftLevelPerVariable = new HashMap<BoogieVar, Integer>();
		ArrayList<HashMap<BoogieVar, Integer>> result = new ArrayList<HashMap<BoogieVar, Integer>>();
		result.add(new HashMap<BoogieVar, Integer>(shiftLevelPerVariable));
		for (LevelAnnotations lvl : pathLvl) {
			determineShiftLevelsFromEdge(shiftLevelPerVariable, lvl, startLevelOnFirstModification);
			result.add(new HashMap<BoogieVar, Integer>(shiftLevelPerVariable));
		}
		assert(result.size() == pathLvl.size() + 1);
		return result;
	}
	
	/** Modifies shiftLevelPerVariable. Determines from given edge level annotation which variables are changed and
	 * adjusts shiftLevelPerVariable which can then be used for SubstitutionManager.substituteSpecificInToOut(). */
	public static void determineShiftLevelsFromEdge(HashMap<BoogieVar, Integer> shiftLevelPerVariable,
			LevelAnnotations edgeLvl, int startLevelOnFirstModification) {
		// determine which variables are modified:
		HashMap<BoogieVar, TermVariable> outVars = edgeLvl.getOutVars();
		HashMap<BoogieVar, TermVariable> inVars = edgeLvl.getInVars();
		// All modified variables have their shift level increased
		// *IF* they don't appear as inVars at the same time (that would throw an exception since substituteInOut should have prevented that)
		for (BoogieVar boogieVar : outVars.keySet()) {
			TermVariable termVar = outVars.get(boogieVar);
			assert(termVar != null);
			if (inVars.get(boogieVar) != termVar) {
				Integer shiftLevel = shiftLevelPerVariable.get(boogieVar);
				if (shiftLevel != null) {
					shiftLevelPerVariable.put(boogieVar, shiftLevel+1);
				} else {
					shiftLevelPerVariable.put(boogieVar, startLevelOnFirstModification);
				}
			} else {
				throw new RuntimeException("outVar "+boogieVar+":"+termVar+" also appears as inVar!"
											+ "Our art unwinding (substituteInOut()) should have made that impossible!");
			}
		}
	}
	
	public static FormulaAndLevelAnnotation shiftFormulaByEdge(Script script, FormulaAndLevelAnnotation formulaAndLvl,
															LevelAnnotations shiftByEdge) {
		HashMap<BoogieVar, Integer> shiftLevelPerVariable = new HashMap<BoogieVar, Integer>();
		determineShiftLevelsFromEdge(shiftLevelPerVariable, shiftByEdge, 1);
		return SubstitutionManager.substituteSpecificInToOut(script, formulaAndLvl, shiftLevelPerVariable, false);
	}
	
	public static FormulaAndLevelAnnotation backshiftFormulaByEdge(Script script, FormulaAndLevelAnnotation formulaAndLvl,
															LevelAnnotations shiftByEdge) {
		HashMap<BoogieVar, Integer> shiftLevelPerVariable = new HashMap<BoogieVar, Integer>();
		determineShiftLevelsFromEdge(shiftLevelPerVariable, shiftByEdge, 1);
		negateShiftLevelMap(shiftLevelPerVariable);
		return SubstitutionManager.substituteSpecificInToOut(script, formulaAndLvl, shiftLevelPerVariable, false);
	}
	
	public static void negateShiftLevelMap(HashMap<BoogieVar, Integer> shiftLevelPerVariable) {
		for (BoogieVar boogieVar : shiftLevelPerVariable.keySet()) {
			int shiftLevel = shiftLevelPerVariable.get(boogieVar);
			shiftLevelPerVariable.put(boogieVar, -shiftLevel);
		}
	}
	
	/** Determines which locations (CFG nodes) can appear more than once in any path.
	 * Needed to know which preceeding locations have to be stored for the ART, since we don't want to
	 * store too much. */
	public static Set<CFGExplicitNode> determineLoopLocations(CFGExplicitNode cfgRootNode) {
		HashSet<CFGExplicitNode> result = new HashSet<CFGExplicitNode>();
		LinkedList<LoopTestNode> stack = new LinkedList<LoopTestNode>();
		assert(cfgRootNode != null);
		stack.push(new LoopTestNode(cfgRootNode, new ArrayList<CFGExplicitNode>()));
		while (!stack.isEmpty()) {
			LoopTestNode currentNode = stack.pop();
			ArrayList<CFGExplicitNode> ancestors = currentNode.getAncestors();
			List<INode> outgoingNodes = currentNode.getNode().getOutgoingNodes();
			if (outgoingNodes != null) {
				for (INode successor : outgoingNodes) {
					CFGExplicitNode successor2 = (CFGExplicitNode) successor;
					ArrayList<CFGExplicitNode> successorAncestors = new ArrayList<CFGExplicitNode>(ancestors);
					successorAncestors.add(currentNode.getNode());
					LoopTestNode successor3 = new LoopTestNode(successor2, successorAncestors);
					if (!result.contains(successor2)) {
						int foundAt = successorAncestors.indexOf(successor2);
						if (foundAt == -1) {
							stack.push(successor3);
						} else {
							for (int i = foundAt; i < successorAncestors.size(); i++) {
								result.add(successorAncestors.get(i));
							}
						}
					}
				}
			}
		}
		return result;
	}
	
	public static String getListOfArtNodeNames(List<UnwindingNode> artNodes) {
		Iterator<UnwindingNode> iterator = artNodes.iterator();
		StringBuilder names = new StringBuilder();
		while (iterator.hasNext()) {
			names.append(iterator.next().getPayload().getName());
			if (iterator.hasNext())
				names.append("; ");
		}
		return names.toString();
	}
	
	public static String artToString(UnwindingNode root) {
		return artToString(root, 0);
	}
	private static String artToString(UnwindingNode root, int indentation) {
		String result = repeat(" ", indentation)+root.getOriginalCFGNode().getPayload().getName()+"|"
						+ HelperMethods.getClauseSet(root);
		List<INode> children = root.getOutgoingNodes();
		if (children == null || children.isEmpty())
			return result;
		result = result + ":\n";
		for (INode child : children) {
			if (child instanceof UnwindingNode) {
				List<IEdge> incomingEdges = child.getIncomingEdges();
				assert(incomingEdges.size() <= 1);
				if (incomingEdges.size() == 1) {
					CFGEdge edge = (CFGEdge) incomingEdges.get(0);
					FormulaAndLevelAnnotation edgeFormulaAndLvl = HelperMethods.getFormulaAndLvlFromArtEdge(edge);
					result = result + repeat(" ", indentation+4) + "==="+edgeFormulaAndLvl+"==>\n";
				}
				result = result + HelperMethods.artToString((UnwindingNode) child, indentation+8)+"\n";
			}
		}
		result = result + repeat(" ", indentation);
		return result;
	}
	
	public static boolean isArtInductive(Script script, UnwindingNode root, Set<UnwindingNode> satErrorLocationArtNodes) {
		LinkedList<UnwindingNode> todo = new LinkedList<UnwindingNode>();
		todo.add(root);
		
		while (!todo.isEmpty()) {
			UnwindingNode node = todo.removeFirst();
			Set<Clause> nodeClauseSet = HelperMethods.getClauseSet(node);
			FormulaAndLevelAnnotation nodeFormulaAndLvl = Clause.buildConjunction(script, nodeClauseSet);
			Term nodeFormula = nodeFormulaAndLvl.getFormula();
			List<IEdge> edgesToChildren = node.getOutgoingEdges();
			if (edgesToChildren == null)
				continue;
			for (IEdge iEdge: edgesToChildren) {
				CFGEdge edgeToChild = (CFGEdge) iEdge;
				FormulaAndLevelAnnotation edgeFormulaAndLvl = HelperMethods.getFormulaAndLvlFromArtEdge(edgeToChild);
				Term edgeFormula = edgeFormulaAndLvl.getFormula();
				LevelAnnotations edgeLvl = edgeFormulaAndLvl.getLevelAnnotation();
				UnwindingNode childNode = (UnwindingNode) edgeToChild.getTarget();
				
				Term childPrimed;
				if (childNode.isErrorLocation() && !satErrorLocationArtNodes.contains(childNode)) {
					childPrimed = script.term("false"); 
				} else {
					Set<Clause> childClauseSet = HelperMethods.getClauseSet(childNode);
					FormulaAndLevelAnnotation childFormulaAndLvl = Clause.buildConjunction(script, childClauseSet);
					FormulaAndLevelAnnotation childPrimedAndLvl = 
							HelperMethods.shiftFormulaByEdge(script, childFormulaAndLvl, edgeLvl);
					childPrimed = childPrimedAndLvl.getFormula();
				}
				
				Term toCheck = script.term("=>", script.term("and", nodeFormula, edgeFormula), childPrimed);
				LBool sat = TreeIC3.checkSat(script, script.term("not", toCheck));
				if (sat != LBool.UNSAT)
					return false;
				todo.addLast(childNode);
			}
		}
		return true;
	}
	
	public static String repeat(String string, int repetitions) {
		StringBuilder builder = new StringBuilder();
		for (int i = 1; i <= repetitions; i++) {
			builder.append(string);
		}
		return builder.toString();
	}
	
	public static void log() {
		log("");
	}
	public static void log(Object object) {
		log(object.toString(), true, false);
	}
	public static void log(Object object, boolean finishLine, boolean asError) {
		log(object.toString(), finishLine, asError);
	}
	public static void log(String message, boolean finishLine, boolean asError) {
		char escape = (char) 27;
		if (asError) {
			if (finishLine) {
				System.out.println(escape+"[31;1m"+message+escape+"[0m");
			} else {
				System.out.print(escape+"[31;1m"+message+escape+"[0m");
			}
		} else {
			if (finishLine) {
				System.out.println(message);
			} else {
				System.out.print(message);
			}
		}
	}
}
