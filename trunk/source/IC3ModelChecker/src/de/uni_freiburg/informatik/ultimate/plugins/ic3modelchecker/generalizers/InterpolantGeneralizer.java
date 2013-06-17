package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.generalizers;

import java.util.HashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.ConstSubstResult;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.HelperMethods;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.SubstitutionManager;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.TreeIC3;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFtoCDNFTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFtoCDNFTransformer.TargetNF;

public class InterpolantGeneralizer implements Generalizer {

	@Override
	public Set<Clause> generalization(Script script, Cube cube, FormulaAndLevelAnnotation clauseSetAndLvl, FormulaAndLevelAnnotation edgeFormulaAndLvl) {
		TreeIC3.logger().debug("InterpolantGeneralizer.generalization() called.");
		LevelAnnotations edgeLvl = edgeFormulaAndLvl.getLevelAnnotation();
		Cube primedCube = cube.toOut(script, edgeLvl);
		LevelAnnotations primedCubeLvl = primedCube.toFormulaAndLvl(script).getLevelAnnotation();
		Term primedCubeTerm = primedCube.toTerm(script);
		Term implyingTerm = script.term("and", clauseSetAndLvl.getFormula(), edgeFormulaAndLvl.getFormula());
		
		script.push(1);
		
		ConstSubstResult substResult1 = SubstitutionManager.substituteFreeVarsToConst(script, implyingTerm, null);
		Term implyingTermConst = substResult1.getSubstTerm();
		HashMap<Term, Term> substMap1 = substResult1.getMap();
		ConstSubstResult substResult2 = SubstitutionManager.substituteFreeVarsToConst(script, primedCubeTerm, substMap1);
		Term primedCubeTermConst = substResult2.getSubstTerm();
		HashMap<Term, Term> substMap2 = substResult2.getMap();
		Term annotatedImplyingTerm = script.annotate(implyingTermConst, new Annotation(":named", "A"));
		Term annotatedPrimedCube = script.annotate(primedCubeTermConst, new Annotation(":named", "B"));
		script.assertTerm(annotatedImplyingTerm);
		script.assertTerm(annotatedPrimedCube);
		LBool sat = script.checkSat();
		if (sat != LBool.UNSAT) {
			throw new RuntimeException("Interpolant generalization: Could not calculate interpolants because conjunction is" +
										" satisfiable / cube is reachable!");
		}
		Term[] interpolants = script.getInterpolants(new Term[]{script.term("A"), script.term("B")});
		assert(interpolants.length == 1);
		Term interpolantWithConstants = interpolants[0];
		
		// Note that the substMap2 contains all substitutions for both implyingTerm and primedCubeTerm,
		// thus we only need that one for resubstitution! 
		HashMap<Term, Term> resubstMap2 = HelperMethods.mirrorMap(substMap2);
		SubstituteTermTransformer substTransformer = new SubstituteTermTransformer();
		Term interpolant = substTransformer.substitute(interpolantWithConstants, resubstMap2);
		script.pop(1);
		
		HashMap<Term, Integer> convertedCache = new HashMap<Term, Integer>();
		NNFTransformer nnfTransformer = new NNFTransformer(convertedCache, -1);
		Term nnfInterpolant = nnfTransformer.transform(interpolant);
		NNFtoCDNFTransformer nnfToCnfTransformer = new NNFtoCDNFTransformer(TargetNF.CNF, convertedCache, -1);
		Term cnfInterpolant = nnfToCnfTransformer.transform(nnfInterpolant);
		LevelAnnotations cnfInterpolantLvl = primedCubeLvl.clone();
		cnfInterpolantLvl.reduceLevelAnnotations(cnfInterpolant);
		FormulaAndLevelAnnotation cnfInterpolantAndLvl = new FormulaAndLevelAnnotation(cnfInterpolant, cnfInterpolantLvl);
		// TODO: We have to shift the interpolant variables backwards!
		cnfInterpolantAndLvl = HelperMethods.backshiftFormulaByEdge(script, cnfInterpolantAndLvl, edgeLvl); 
		return Clause.extractClauseSetFromCNF(cnfInterpolantAndLvl);
	}
}
