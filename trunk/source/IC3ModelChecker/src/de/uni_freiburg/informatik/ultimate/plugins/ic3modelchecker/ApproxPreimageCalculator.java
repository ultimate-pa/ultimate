package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers.SubstituteTermTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.parser.SMTParserInterface;

public class ApproxPreimageCalculator {
	/** Retrieves an underapproximation for the given formula which should be
	 * of the form "transition and bad cube". The formula should only contain
	 * inVars and outVars and no quantifiers. */
	public static Set<Cube> preimage(FormulaAndLevelAnnotation formulaAndLvl, Script script) {
		Term term = formulaAndLvl.getFormula();
		LevelAnnotations levelAnnotation = formulaAndLvl.getLevelAnnotation();
		// NOTE: Mathematica syntax: Exists[{varlist}, formula]
		// retrieve satisfying evaluation
		HashSet<TermVariable> outVars = new HashSet<TermVariable>(levelAnnotation.getOutVars().values());
		HashSet<TermVariable> substVars = new HashSet<TermVariable>(levelAnnotation.getInVars().values());
		HashSet<TermVariable> unclassifiedVars = new HashSet<TermVariable>(levelAnnotation.getVars());
		unclassifiedVars.removeAll(outVars);
		unclassifiedVars.removeAll(substVars);
		for (TermVariable unclassifiedVar : unclassifiedVars) {
			TreeIC3.logger().warn("preimage(): var "+unclassifiedVar.getName()+" is neither invar nor outvar!");
		}
		substVars.addAll(unclassifiedVars);
		
		// To get the preimage, we will have to existentially quantify over the outvars
		// and substitute the substvars by constants
		String mathTerm = MathPrinter.convert(term);
		String mathTerm2;
		if (!outVars.isEmpty()) {
			String existPrefix = MathPrinter.createExistPrefix(outVars);
			mathTerm2 = existPrefix+mathTerm+"]";
		} else {
			mathTerm2 = mathTerm;
		}
		TreeIC3.logger().debug("ApproxPreimage: Get preimage of "+mathTerm2);
		// script.push() here because we will introduce constants
		script.push(1);
		// constant substitution
		ConstSubstResult result = SubstitutionManager.substituteVarsToConst(script, term, substVars, null);
		// call Mjollnir
		Term preimageWithConstants;
		try {
			Process mjollnir = Runtime.getRuntime().exec(
					"/home/leys/Mjollnir/trunk/mjollnir --input-syntax math --output-syntax smtlib --full-simplify");
			InputStreamReader output = new InputStreamReader(mjollnir.getInputStream());
			InputStreamReader error = new InputStreamReader(mjollnir.getErrorStream());
			PrintWriter input = new PrintWriter(mjollnir.getOutputStream());
			input.println(mathTerm2);
			input.flush();
			input.close();
			TreeIC3.logger().debug("Waiting for Mjollnir");
			while (!error.ready() && !output.ready()) {
				// Wait until either error or output is ready
			}
			TreeIC3.logger().debug("");
			if (error.ready()) {
				BufferedReader reader = new BufferedReader(error);
				StringBuilder errorMessage = new StringBuilder();
				while (error.ready())
					errorMessage.append(reader.readLine()+"\n");
				throw new RuntimeException("Mjollnir error! Message:\n"+errorMessage);
			}
			assert(output.ready());
			TreeIC3.logger().debug("Mjollnir terminated, parse...");
			preimageWithConstants = SMTParserInterface.parse(output, script);
		} catch(IOException e) {
			throw new RuntimeException("Mjollnir communication caused an IO exception!");
		}
		// Resubstitute the constants in the preimage:
		HashMap<Term, Term> resubstMap = HelperMethods.mirrorMap(result.getMap());
		SubstituteTermTransformer substTransformer = new SubstituteTermTransformer();
		Term preimage = substTransformer.substitute(preimageWithConstants, resubstMap);
		
		// script.pop() here since we don't need the constants anymore
		script.pop(1);
		LevelAnnotations preimageLvl = levelAnnotation.clone();
		preimageLvl.reduceLevelAnnotations(preimage);
		FormulaAndLevelAnnotation preimageAndLvl = new FormulaAndLevelAnnotation(preimage, preimageLvl);
		TreeIC3.logger().debug("ApproxPreimage: Preimage= "+preimageAndLvl);
		// We don't need to call nnf and dnf transformers anymore because
		// Mjollnir only returns formulas in dnf
		if (preimage.equals(script.term("false")))
			TreeIC3.logger().warn("preimage(): Got false as preimage!");
		return Cube.extractCubeSetFromDNF(preimageAndLvl);
	}
}
