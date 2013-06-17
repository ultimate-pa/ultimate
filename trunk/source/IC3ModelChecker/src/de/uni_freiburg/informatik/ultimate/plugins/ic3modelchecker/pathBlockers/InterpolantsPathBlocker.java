package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.pathBlockers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.ConcatenationResult;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.ConstSubstResult;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.HelperMethods;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.SubstitutionManager;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeIC3;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeSizeCalculator;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulasAndLevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.UnwindingNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFtoCDNFTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFtoCDNFTransformer.TargetNF;

public class InterpolantsPathBlocker {

	public TreeIC3BlockPathResult treeIC3BlockPath(TreeIC3 parent, List<UnwindingNode> satErrorPath, int exceedingFactor) {
		TreeIC3.logger().debug("InterpolantsPathBlocker.treeIC3BlockPath() called.");
		Script script = parent.getScript();
		assert(satErrorPath.size() >= 2);
		FormulasAndLevelAnnotations edgeFormulasAndLvl = 
				HelperMethods.extractEdgeFormulasAndLvlFromArtPath(satErrorPath);
		
		ConcatenationResult concatenation = HelperMethods.getConcatenation(new HashMap<BoogieVar, Integer>(), edgeFormulasAndLvl, script);
		TreeIC3.logger().debug("Concatenation: "+concatenation.formulasAndLvl);
		ArrayList<Term> formulas = concatenation.formulasAndLvl.getEdgeFormulas();
		ArrayList<LevelAnnotations> lvl = concatenation.formulasAndLvl.getLevelAnnotations();
		ArrayList<HashMap<BoogieVar, Integer>> shiftLevelsForPath = concatenation.shiftLevelsForPath;
		assert(shiftLevelsForPath.size() == edgeFormulasAndLvl.size() + 1);
		
		/* The interpolants are generated between the following formulas:
		 * first clause set and outgoing edge formula;
		 * next edge formula;
		 * ...;
		 * next edge formula;
		 * last edge formula and last clause set where it leads to;   
		 */
		/* The Level Annotation for interpolants[i] should be the merged lvl[0..i], though I'm not sure
		 * 
		 */
		
		Set<Clause> firstClauseSet = HelperMethods.getClauseSet(satErrorPath.get(0));
		FormulaAndLevelAnnotation firstClauseSetFormulaAndLvl = Clause.buildConjunction(script, firstClauseSet);
		Set<Clause> lastClauseSet = HelperMethods.getClauseSet(satErrorPath.get(satErrorPath.size()-1));
		FormulaAndLevelAnnotation lastClauseSetFormulaAndLvl = Clause.buildConjunction(script, lastClauseSet);
		FormulaAndLevelAnnotation lastClauseSetFormulaAndLvlPrimed = SubstitutionManager.substituteSpecificInToOut(script,
										lastClauseSetFormulaAndLvl, shiftLevelsForPath.get(shiftLevelsForPath.size()-1), false);
		
		Term[] namedFormulas = new Term[formulas.size()];
		HashMap<Term, Term> alreadyDeclared = new HashMap<Term, Term>();
		script.push(1);
		
		for (int i = 0; i < formulas.size(); i++) {
			// Substitute free vars by constants
			Term formula;
			if (i == 0) {
				formula = script.term("and", formulas.get(i), firstClauseSetFormulaAndLvl.getFormula());
			} else if (i == formulas.size()-1) {
				formula = script.term("and", formulas.get(i), lastClauseSetFormulaAndLvlPrimed.getFormula());
			} else {
				formula = formulas.get(i);	
			}
			
			ConstSubstResult constSubst = SubstitutionManager.substituteFreeVarsToConst(script, formula, alreadyDeclared);
			Term constFormula = constSubst.getSubstTerm();
			String annotatedName = "A"+i;
			// annotate edge for interpolation calculation
			Term annotatedFormula = script.annotate(constFormula, new Annotation(":named", annotatedName));
			namedFormulas[i] = script.term(annotatedName);
			script.assertTerm(annotatedFormula);
			alreadyDeclared = constSubst.getMap();
		}

		LBool sat = script.checkSat();
		if (sat != LBool.UNSAT) {
			script.pop(1);
			// counterexample found, error path is feasible
			return new TreeIC3BlockPathResult(satErrorPath, null, null);
		}
		
		Term[] constInterpolants = script.getInterpolants(namedFormulas);
		assert(constInterpolants.length == namedFormulas.length - 1);
		
		// Resubstitute constants in interpolants
		HashMap<Term, Term> resubstMap = HelperMethods.mirrorMap(alreadyDeclared);
		SubstituteTermTransformer substTransformer = new SubstituteTermTransformer();
		ArrayList<Term> interpolants = new ArrayList<Term>();
		for (Term constInterpolant : constInterpolants) {
			Term interpolant = substTransformer.substitute(constInterpolant, resubstMap);
			interpolants.add(interpolant);
		}
		script.pop(1);
		
		// Add level annotations, backshift interpolants by shiftLevelsForPath above
		ArrayList<FormulaAndLevelAnnotation> backshifted = new ArrayList<FormulaAndLevelAnnotation>();
		ArrayList<LevelAnnotations> levelAnnotationList = new ArrayList<>();
		for (int i = 0; i < interpolants.size(); i++) {
			Term interpolant = interpolants.get(i);
			
			if (i == 0) {
				levelAnnotationList.add(firstClauseSetFormulaAndLvl.getLevelAnnotation());
			}
			levelAnnotationList.add(lvl.get(i));
			LevelAnnotations interpolantLvl = LevelAnnotations.getMerged(levelAnnotationList, interpolant);
			
			FormulaAndLevelAnnotation interpolantAndLvl = new FormulaAndLevelAnnotation(interpolant, interpolantLvl);
			TreeIC3.logger().debug("Raw interpolant: "+interpolantAndLvl);
			HashMap<BoogieVar, Integer> shiftedBy = shiftLevelsForPath.get(i+1);
			HelperMethods.negateShiftLevelMap(shiftedBy);
			backshifted.add(SubstitutionManager.substituteSpecificInToOut(script, interpolantAndLvl, shiftedBy, false));
		}
		
		// extract clause sets from interpolants
		TreeIC3.logger().debug("backshifted interpolants: "+backshifted);
		TreeIC3.logger().debug("Now apply nnfTransformer and nnfToCnfTransformer...");
		
		ArrayList<FormulaAndLevelAnnotation> cnfInterpolants = new ArrayList<>();
		for (FormulaAndLevelAnnotation interpolant : backshifted) {
			HashMap<Term, Integer> convertedCache = new HashMap<Term, Integer>();
			int originalTreeSize = TreeSizeCalculator.calcTreeSize(interpolant.getFormula(), convertedCache);
			int maxTreeSizeIncrease = (exceedingFactor - 1) * originalTreeSize;
			NNFTransformer nnfTransformer = new NNFTransformer(convertedCache, maxTreeSizeIncrease);
			NNFtoCDNFTransformer nnfToCnfTransformer = new NNFtoCDNFTransformer(TargetNF.CNF, convertedCache, maxTreeSizeIncrease);
			nnfToCnfTransformer.setCurrentTermSizeIncrease(nnfTransformer.getCurrentTermSizeIncrease());
			FormulaAndLevelAnnotation nnfInterpolant = new FormulaAndLevelAnnotation(nnfTransformer.transform(interpolant.getFormula()), interpolant.getLevelAnnotation());
			cnfInterpolants.add(new FormulaAndLevelAnnotation(nnfToCnfTransformer.transform(nnfInterpolant.getFormula()), nnfInterpolant.getLevelAnnotation()));
		}
		TreeIC3.logger().debug("Interpolants in CNF: "+cnfInterpolants);
		ArrayList<Set<Clause>> traceOfClauseSets = new ArrayList<>();
		// First and last node shouldn't get any new clauses -> add empty sets
		traceOfClauseSets.add(new HashSet<Clause>()); // empty clause set == "true"
		for (FormulaAndLevelAnnotation interpolant : cnfInterpolants)
			traceOfClauseSets.add(Clause.extractClauseSetFromCNF(interpolant));
		Set<Clause> setContainingEmptyClause = new HashSet<Clause>();
		setContainingEmptyClause.add(new Clause());
		traceOfClauseSets.add(new HashSet<Clause>()); // empty clause set == "true"
		assert(traceOfClauseSets.size() == satErrorPath.size());
		return new TreeIC3BlockPathResult(null, traceOfClauseSets, edgeFormulasAndLvl);
	}
}
