package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.HelperMethods;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeIC3;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.generalizers.Generalizer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulasAndLevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.UnwindingNode;

public class PreimagesPathBlocker {

	/** Called by pathBlocking(), pure. 
	 * Tries to block the given error path and returns trace,
	 * or else returns a counterexample trace. <br/>
	 * Precondition: Last clause set must be satisfiable, or else we get an endless loop! */
	public TreeIC3BlockPathResult treeIC3BlockPath(TreeIC3 parent, List<UnwindingNode> satErrorPath) {
		Script script = parent.getScript();
		assert(satErrorPath.size() >= 2);
		TreeIC3.logger().debug("Trying to block the path");
		TreeIC3.logger().debug(HelperMethods.getListOfArtNodeNames(satErrorPath));
		TreeIC3.logger().debug("");
		ArrayList<Set<Clause>> trace = HelperMethods.extractClauseSetsFromPath(satErrorPath, true);
		FormulasAndLevelAnnotations edgeFormulasAndLvl = 
				HelperMethods.extractEdgeFormulasAndLvlFromArtPath(satErrorPath);
		ArrayList<Term> edgeFormulas = edgeFormulasAndLvl.getEdgeFormulas();
		ArrayList<LevelAnnotations> edgeLevelAnnotations = edgeFormulasAndLvl.getLevelAnnotations();
		int traceSize = trace.size();
		int edgesSize = edgeFormulas.size();
		TreeIC3.logger().debug("Blocking: The clause sets of the satisfiable error path are");
		for (int i = 0; i < trace.size(); i++)
			TreeIC3.logger().debug(trace.get(i));
		TreeIC3.logger().debug("Blocking: The edge formulas of the satisfiable error path are");
		TreeIC3.logger().debug(edgeFormulasAndLvl);
		TreeIC3.logger().debug("Trace contains "+traceSize+" elements, edgeFormulas contains "+edgesSize+" elements.");
		
		assert(traceSize == edgesSize+1);

		
		while (parent.existsUnsatPair(trace, edgeFormulasAndLvl) == -1) {
			Stack<ProofObligation> q = new Stack<ProofObligation>();
			// There's an error in the paper: It should be approx-preimage(trace.prelast and lastEdge and trace.last').
			FormulaAndLevelAnnotation tracePreLastAndLvl = Clause.buildConjunction(script, trace.get(traceSize-2));
			Term lastEdgeFormula = edgeFormulas.get(edgesSize-1);
			LevelAnnotations lastEdgeLvl = edgeLevelAnnotations.get(edgesSize-1);
			FormulaAndLevelAnnotation traceLastAndLvl = Clause.buildConjunction(script, trace.get(traceSize-1));
			// do priming to the last element in the trace DEPENDING on what is modified in the edge formula:
			FormulaAndLevelAnnotation traceLastPrimeAndLvl = HelperMethods.shiftFormulaByEdge(script, traceLastAndLvl, lastEdgeLvl);

			Term image = script.term("and", tracePreLastAndLvl.getFormula(), lastEdgeFormula, 
											traceLastPrimeAndLvl.getFormula());
			ArrayList<LevelAnnotations> levelAnnotations = new ArrayList<LevelAnnotations>();
			levelAnnotations.add(tracePreLastAndLvl.getLevelAnnotation());
			levelAnnotations.add(lastEdgeLvl);
			levelAnnotations.add(traceLastPrimeAndLvl.getLevelAnnotation());
			LevelAnnotations imageLevelAnnotations = LevelAnnotations.getMerged(levelAnnotations, image);
			// TODO: Sometimes there seem to be variables in lvl which don't appear anymore in the formula 

			FormulaAndLevelAnnotation imageAndLevelAnnotation = new FormulaAndLevelAnnotation(image, imageLevelAnnotations);
			TreeIC3.logger().debug("Determine preimage cubes of "+imageAndLevelAnnotation);
			Set<Cube> badStates = TreeIC3.approxPreimage(imageAndLevelAnnotation, script);
			assert(!badStates.isEmpty());
			// Now these cubes have to be blocked themselves while stepping from
			// trace.size()-3 to trace.size()-2, that means
			// vom vorvorletzten zum vorletzten Element
			// ==> index means: cube has to be blocked while stepping from
			// trace[index-1] to trace[index]
			// that means the blocking index is also the index for trace access 
			for (Cube bad : badStates) {
				q.push(new ProofObligation(bad, trace.size()-2));
			}
			while (!q.isEmpty()) {
				TreeIC3.logger().debug("There are "+q.size()+" proof obligations to handle");
				ProofObligation proofObligation = q.peek();
				Cube cube = proofObligation.getCube();
				int index = proofObligation.getIndex();
				TreeIC3.logger().debug("Trying to block cube ("+cube+", "+index+")");
				if (index == 0)
					return new TreeIC3BlockPathResult(satErrorPath, null, null);
				// TODO: Attention: Same problem as we had it, we only may use primed variables if they are modified
				// at the edge. If the edge is "true", then the variables don't change and we either have to add "xOut = xIn"
				// or we don't prime the variable
				FormulaAndLevelAnnotation edgeFormulaAndLvl = edgeFormulasAndLvl.getFormulaAndLevel(index-1);
				Term edgeFormula = edgeFormulaAndLvl.getFormula();
				LevelAnnotations edgeLvl = edgeFormulaAndLvl.getLevelAnnotation();
				Cube cubePrimed = cube.toOut(script, edgeLvl);
				TreeIC3.logger().debug("cube is "+cube+", while cube' is "+cubePrimed);
				FormulaAndLevelAnnotation cubePrimedFormulaAndLvl = cubePrimed.toFormulaAndLvl(script);
				Term cubePrimedFormula = cubePrimedFormulaAndLvl.getFormula();
				LevelAnnotations cubePrimedLvl = cubePrimedFormulaAndLvl.getLevelAnnotation();
				
				FormulaAndLevelAnnotation conjunctionAndLvl = Clause.buildConjunction(script, trace.get(index-1)); 
				Term conjunction = conjunctionAndLvl.getFormula();
				LevelAnnotations conjunctionLvl = conjunctionAndLvl.getLevelAnnotation();
				Term toCheck = script.term("=>", script.term("and", conjunction,
						edgeFormula), script.term("not", cubePrimedFormula)); 

				LBool result = TreeIC3.checkSat(script, script.term("not", toCheck));
				
				if (result == LBool.UNSAT) {
					//toCheck is valid:
					TreeIC3.logger().debug("Cube is blocked since "+conjunctionAndLvl
							+" and "+edgeFormulasAndLvl.getFormulaAndLevel(index-1)+" imply (not "+cubePrimed+")");
					// cube is blocked, discard proof obligation
					q.pop();
					Generalizer generalizer = parent.getGeneralizer();
					Set<Clause> g = generalizer.generalization(script, cube, conjunctionAndLvl, edgeFormulaAndLvl);
					TreeIC3.logger().debug("Add generalization "+g+" to "+trace.get(index));
					trace.get(index).addAll(g);
				} else {
					TreeIC3.logger().debug("Cube is not blocked since (" + conjunctionAndLvl
							+ " and "+edgeFormulasAndLvl.getFormulaAndLevel(index-1)+") don't imply (not "+cubePrimed+")");
					Term nodeAndEdgeAndCubeFormula = script.term("and", conjunction,
							edgeFormula, cubePrimedFormula);
					List<LevelAnnotations> levelAnnotationList = new ArrayList<LevelAnnotations>();
					levelAnnotationList.add(conjunctionLvl);
					levelAnnotationList.add(edgeLvl);
					levelAnnotationList.add(cubePrimedLvl);
					LevelAnnotations nodeAndEdgeAndCubeLvl = LevelAnnotations.getMerged(levelAnnotationList, null);
					FormulaAndLevelAnnotation formulaAndLvl = new FormulaAndLevelAnnotation(nodeAndEdgeAndCubeFormula,
																						nodeAndEdgeAndCubeLvl);
					TreeIC3.logger().debug("Therefore, we will push all preimage cubes of "+formulaAndLvl+" onto the stack.");
					Set<Cube> cubes = TreeIC3.approxPreimage(formulaAndLvl, script);
					for (Cube cube2 : cubes) {
						if (cube2.toTerm(script).equals(script.term("false")))
							TreeIC3.logger().warn("treeIC3BlockPath(): approxPreimage returned false!");
						TreeIC3.logger().debug("Pushing "+cube2+" with index "+(index-1)+" onto the stack.");
						q.push(new ProofObligation(cube2, index-1));
					}
				}
				
			}
		}
		return new TreeIC3BlockPathResult(null, trace, new FormulasAndLevelAnnotations(edgeFormulas, edgeLevelAnnotations));
	}
}
