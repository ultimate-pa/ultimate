package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.io.ByteArrayInputStream;
import java.io.InputStreamReader;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Clause;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Cube;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.FormulaAndLevelAnnotation;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.Literal;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.logic.LevelAnnotations;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.ExceedsMaxTreeSizeException;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFtoCDNFTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.nfTransformers.NNFtoCDNFTransformer.TargetNF;
import de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker.parser.SMTParserInterface;

public class Tests {
	public static void equalityTests(Script script) {
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		BoogieVar boogieA = new BoogieVar("a", null, null, false);
		TermVariable a = theory.createTermVariable("v_a", intSort);
		BoogieVar boogieA2 = new BoogieVar("a", null, null, false);
		TermVariable a2 = theory.createTermVariable("v_a", intSort);
		BoogieVar boogieB = new BoogieVar("b", null, null, false);
		TermVariable b = theory.createTermVariable("v_b", intSort);
		
		Term t1 = script.term("=", a, a);
		Term t2 = script.term("=", a2, a2);
		Term t3 = script.term("=", b, b);
		assert(t1.equals(t2));
		assert(t1.hashCode() == t2.hashCode());
		HashSet<Term> set = new HashSet<Term>();
		set.add(t1);
		set.add(t2);
		assert(set.size() == 1);
		
		HashSet<TermVariable> allVars1 = new HashSet<TermVariable>();
		allVars1.add(a);
		HashMap<Integer, HashMap<BoogieVar, TermVariable>> leveledVars1 = new HashMap<Integer, HashMap<BoogieVar, TermVariable>>();
		HashMap<BoogieVar, TermVariable> level = new HashMap<>();
		level.put(boogieA, a);
		leveledVars1.put(0, level);
		LevelAnnotations lvl1 = new LevelAnnotations(script, allVars1, leveledVars1); 
		FormulaAndLevelAnnotation formulaAndLvl1 = new FormulaAndLevelAnnotation(t1, lvl1);
		
		HashSet<TermVariable> allVars2 = new HashSet<TermVariable>();
		allVars2.add(a2);
		HashMap<Integer, HashMap<BoogieVar, TermVariable>> leveledVars2 = new HashMap<Integer, HashMap<BoogieVar, TermVariable>>();
		level = new HashMap<>();
		level.put(boogieA2, a2);
		leveledVars2.put(0, level);
		LevelAnnotations lvl2 = new LevelAnnotations(script, allVars2, leveledVars2); 
		FormulaAndLevelAnnotation formulaAndLvl2 = new FormulaAndLevelAnnotation(t2, lvl2);
		assert(lvl1.equals(lvl2));
		assert(lvl1.hashCode() == lvl2.hashCode());
		assert(formulaAndLvl1.equals(formulaAndLvl2));
		assert(formulaAndLvl1.hashCode() == formulaAndLvl2.hashCode());
		
		Literal literal1 = new Literal(false, formulaAndLvl1);
		Literal literal2 = new Literal(false, formulaAndLvl2);
		assert(literal1.equals(literal2));
		assert(literal1.hashCode() == literal2.hashCode());
		
		Clause clause1 = new Clause(literal1);
		Clause clause2 = new Clause(literal2);
		assert(clause1.equals(clause2));
		assert(clause1.hashCode() == clause2.hashCode());
		
		HashSet<Clause> clauseSet1 = new HashSet<Clause>();
		clauseSet1.add(clause1);
		HashSet<Clause> clauseSet2 = new HashSet<Clause>();
		clauseSet2.add(clause2);
		assert(clauseSet1.equals(clauseSet2));
		assert(clauseSet1.hashCode() == clauseSet2.hashCode());
	}
	
	public static void createSimplifiedFormulaTests(Script script) {
		// Given an edge with formula "xOut = xIn + 1" leading to the node with formula "xIn = 0 and yIn > 1",
		// check what the representation would be if we move all formulas into the edge.
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		BoogieVar boogieX = new BoogieVar("x", null, null, false);
		BoogieVar boogieY = new BoogieVar("y", null, null, false);

		TermVariable edgeXIn = theory.createTermVariable("v_x_1", intSort);
		TermVariable edgeXOut = theory.createTermVariable("v_x_2", intSort);
		Term edgeFormula = script.term("=", edgeXOut, script.term("+", edgeXIn, script.numeral("1")));
		SMTEdgeAnnotations edgeSmt = new SMTEdgeAnnotations();
		edgeSmt.setScript(script);
		edgeSmt.getVars().add(edgeXIn);
		edgeSmt.getVars().add(edgeXOut);
		edgeSmt.getInVars().put(boogieX, edgeXIn);
		edgeSmt.getOutVars().put(boogieX, edgeXOut);
		FormulaAndLevelAnnotation edgeFormulaAndLvl = new FormulaAndLevelAnnotation(edgeFormula, new LevelAnnotations(edgeSmt, null));
		
		TermVariable nodeXIn = theory.createTermVariable("v_x_5", intSort);
		TermVariable nodeYIn = theory.createTermVariable("v_y_1", intSort);
		Term nodeFormula = script.term("and", script.term("=", nodeXIn, script.numeral("0")),
										script.term(">", nodeYIn, script.numeral("1")));
		SMTNodeAnnotations nodeSmt = new SMTNodeAnnotations();
		nodeSmt.setScript(script);
		nodeSmt.getVars().add(nodeXIn);
		nodeSmt.getVars().add(nodeYIn);
		nodeSmt.getInVars().put(boogieX, nodeXIn);
		nodeSmt.getInVars().put(boogieY, nodeYIn);
		FormulaAndLevelAnnotation nodeFormulaAndLvl = new FormulaAndLevelAnnotation(nodeFormula, new LevelAnnotations(null, nodeSmt));
		
		FormulaAndLevelAnnotation result = HelperMethods.createSimplifiedFormula(script, edgeFormulaAndLvl, nodeFormulaAndLvl);
		
		String expected = 
			"(and (= ^1^xL1 (+ ^0^xL0 1)) (= ^1^xL1 0) (> ^0^yL0 1))";
		assert(result.toString().equals(expected));
	}
	
	
	public static void termSizeCalculatorTests(Script script) {
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		TermVariable xVar = theory.createTermVariable("x", intSort);
		assert(TreeSizeCalculator.calcTreeSize(xVar, null) == 0);
		
		Term conjunction = script.term("and", script.term("true"), script.term("true"));
		assert(TreeSizeCalculator.calcTreeSize(conjunction, null) == 1);

		Term term = script.term("<", xVar, xVar);
		assert(TreeSizeCalculator.calcTreeSize(term, null) == 0);

		Term term2 = script.term("or", script.term("<", xVar, xVar), script.term("<", xVar, xVar));
		assert(TreeSizeCalculator.calcTreeSize(term2, null) == 1);
	}
	
	
	public static void nnfTransformerTests(Script script) {
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		TermVariable a = theory.createTermVariable("a", intSort);
		TermVariable b = theory.createTermVariable("b", intSort);
		TermVariable c = theory.createTermVariable("c", intSort);
		Term toNnf = script.term("not", script.term("not", script.term("=", a, b)));
		HashMap<Term, Integer> convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toNnf, convertedCache) == 0);
		// toNnf: (not (not (= a b)))
		NNFTransformer nnfTransformer = new NNFTransformer(convertedCache, 0);
		Term nnfTerm = nnfTransformer.transform(toNnf);
		assert(nnfTerm.toStringDirect().equals("(= a b)"));
		assert(nnfTransformer.getCurrentTermSizeIncrease() == 0);
		assert(TreeSizeCalculator.calcTreeSize(nnfTerm, convertedCache) == 0);
		
		Term toNnf2 = script.term("not", toNnf);
		// toNnf2: (not (not (not (= a b))))
		convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toNnf2, convertedCache) == 0);
		nnfTransformer = new NNFTransformer(convertedCache, 0);
		Term nnfTerm2 = nnfTransformer.transform(toNnf2);
		TreeIC3.logger().debug("nnfTerm2: "+nnfTerm2.toStringDirect());
		assert(nnfTerm2.toStringDirect().equals("(not (= a b))"));
		assert(nnfTransformer.getCurrentTermSizeIncrease() == 0);
		assert(TreeSizeCalculator.calcTreeSize(nnfTerm2, convertedCache) == 0);
		
		Term toNnf3 = script.term("not", script.term("and", script.term("not", script.term("and", 
				script.term("=", a, a), script.term("=", b, b))), script.term("not", script.term("=", c, c))));
		// toNnf3: (not (and (not (and (= a a), (= b b))), (not (= c c))))
		convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toNnf3, convertedCache) == 2);
		nnfTransformer = new NNFTransformer(convertedCache, 0);
		Term nnfTerm3 = nnfTransformer.transform(toNnf3);
		TreeIC3.logger().debug("nnfTerm3: "+nnfTerm3.toStringDirect());
		assert(nnfTerm3.toStringDirect().equals("(or (and (= a a) (= b b)) (= c c))"));
		assert(nnfTransformer.getCurrentTermSizeIncrease() == 0);
		assert(TreeSizeCalculator.calcTreeSize(nnfTerm3, convertedCache) == 2);
		
		Term toNnf4 = script.term("not", script.term("=>", script.term("=", a, a), 
				script.term("=", b, b), script.term("=", c, c)));
		// toNnf4: (not (=> (= a a) (= b b) (= c c)))
		convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toNnf4, convertedCache) == 2);
		nnfTransformer = new NNFTransformer(convertedCache, 0);
		Term nnfTerm4 = nnfTransformer.transform(toNnf4);
		TreeIC3.logger().debug("nnfTerm4: "+nnfTerm4.toStringDirect());
		TreeIC3.logger().debug("nnfTerm4 in mathematica: "+MathPrinter.convert(nnfTerm4));
		assert(nnfTerm4.toStringDirect().equals("(and (= a a) (= b b) (not (= c c)))"));
		assert(nnfTransformer.getCurrentTermSizeIncrease() == 0);
		assert(TreeSizeCalculator.calcTreeSize(nnfTerm4, convertedCache) == 2);
		
		Term toNnf5 = script.term("not", script.term("xor", script.term("=", a, a), script.term("=", b, b), script.term("=", c, c)));
		// toNnf5: (not (xor (= a a) (= b b) (= c c)))
		convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toNnf5, convertedCache) == 2);
		nnfTransformer = new NNFTransformer(convertedCache, 7);
		Term nnfTerm5 = nnfTransformer.transform(toNnf5);
		TreeIC3.logger().debug("nnfTerm5: "+nnfTerm5.toStringDirect());		
		assert(nnfTerm5.toStringDirect().equals("(or (and (and (or (= a a) (= b b)) (or (not (= a a)) (not (= b b)))) (= c c)) (and (or (and (= a a) (= b b)) (and (not (= a a)) (not (= b b)))) (not (= c c))))"));
		assert(nnfTransformer.getCurrentTermSizeIncrease() == 7);
		assert(TreeSizeCalculator.calcTreeSize(nnfTerm5, convertedCache) == 9);
		try {
			new NNFTransformer(convertedCache, 6).transform(toNnf5);
			assert(false);
		} catch (ExceedsMaxTreeSizeException e) {
			TreeIC3.logger().debug("ExceedsMaxTreeSizeException successfully triggered in test.");
		}
		
		Term atomar1 = script.term(">", a, b);
		Term atomar2 = script.term(">", b, c);
		Term atomar3 = script.term(">", c, a);
		Term toNnf6 = script.term("ite", theory.TRUE, script.term("=", atomar1, atomar2, atomar3), script.term("distinct", atomar1, atomar2, atomar3));
		// toNnf6: (ite true (= (> a b) (> b c) (> c a)) (distinct (> a b) (> b c) (> c a)))
		convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toNnf6, convertedCache) == 5);
		nnfTransformer = new NNFTransformer(convertedCache, -1);
		Term nnfTerm6 = nnfTransformer.transform(toNnf6);
		TreeIC3.logger().debug("nnfTerm6: "+nnfTerm6.toStringDirect());
		
	}
	
	
	
	public static void dnfTransformerTests(Script script) {
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		TermVariable a = theory.createTermVariable("a", intSort);
		TermVariable b = theory.createTermVariable("b", intSort);
		TermVariable c = theory.createTermVariable("c", intSort);
		Term toDnf = script.term("or", script.term("=", a, a), script.term("or", 
				script.term("not", script.term("=", b, b)),	script.term("=", c, c)));
		// toDnf: (or (= a a) (or (not (= b b)) (= c c)))
		HashMap<Term, Integer> convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toDnf, convertedCache) == 2);
		NNFtoCDNFTransformer dnfTransformer = new NNFtoCDNFTransformer(TargetNF.DNF, convertedCache, 0);
		Term dnfTerm = dnfTransformer.transform(toDnf);
		TreeIC3.logger().debug("dnfTerm: "+dnfTerm.toStringDirect());
		assert(dnfTerm.toStringDirect().equals("(or (= a a) (not (= b b)) (= c c))"));
		assert(dnfTransformer.getCurrentTermSizeIncrease() == 0);
		assert(TreeSizeCalculator.calcTreeSize(dnfTerm, convertedCache) == 2);
	}
	
	
	
	public static void nnfAndDnfTransformerTests(Script script) {
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		TermVariable x = theory.createTermVariable("x", intSort);
		TermVariable y = theory.createTermVariable("y", intSort);
		Term toDnf = script.term("not", script.term("or", script.term("=", x, y), script.term("and",
				script.term("=", x, x), script.term("=", y, y))));
		// toDnf: (not (or (= x y) (and (= x x) (= y y))))
		TreeIC3.logger().debug("before: "+toDnf.toStringDirect());
		HashMap<Term, Integer> convertedCache = new HashMap<Term, Integer>();
		assert(TreeSizeCalculator.calcTreeSize(toDnf, convertedCache) == 2);
		NNFTransformer nnfTransformer = new NNFTransformer(convertedCache, 0);
		Term nnfTerm = nnfTransformer.transform(toDnf);
		assert(nnfTerm.toStringDirect().equals("(and (not (= x y)) (or (not (= x x)) (not (= y y))))"));
		assert(nnfTransformer.getCurrentTermSizeIncrease() == 0);
		assert(TreeSizeCalculator.calcTreeSize(nnfTerm, convertedCache) == 2);
		TreeIC3.logger().debug("NNF: "+nnfTerm.toStringDirect());
		
		NNFtoCDNFTransformer dnfTransformer = new NNFtoCDNFTransformer(TargetNF.DNF, convertedCache, 1);
		Term dnfTerm = dnfTransformer.transform(nnfTerm);
		assert(dnfTerm.toStringDirect().
				equals("(or (and (not (= x y)) (not (= x x))) (and (not (= x y)) (not (= y y))))"));
		assert(dnfTransformer.getCurrentTermSizeIncrease() == 1);
		assert(TreeSizeCalculator.calcTreeSize(dnfTerm, convertedCache) == 3);
		TreeIC3.logger().debug("DNF: "+dnfTerm.toStringDirect());
		try {
			new NNFtoCDNFTransformer(TargetNF.DNF, convertedCache, 0).transform(nnfTerm);
			assert(false);
		} catch (ExceedsMaxTreeSizeException e) {
			TreeIC3.logger().debug("ExceedsMaxTreeSizeException successfully triggered in test.");
		}
	}
	
	
	
	public static void approxPreimageTests(Script script) {
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		BoogieVar xBoogie = new BoogieVar("x", null, null, false);
		BoogieVar yBoogie = new BoogieVar("y", null, null, false);
		TermVariable x_in = theory.createTermVariable("x"+Settings.inVarSuffix, intSort);
		TermVariable x_out = theory.createTermVariable("x"+Settings.outVarSuffix, intSort);
		TermVariable y_in = theory.createTermVariable("y"+Settings.inVarSuffix, intSort);
		TermVariable y_out = theory.createTermVariable("y"+Settings.outVarSuffix, intSort);
		LevelAnnotations levelAnnotation = new LevelAnnotations(script);
		HashMap<BoogieVar, TermVariable> inVars = levelAnnotation.getInVars();
		HashMap<BoogieVar, TermVariable> outVars = levelAnnotation.getOutVars();
		inVars.put(xBoogie, x_in);
		inVars.put(yBoogie, y_in);
		outVars.put(xBoogie, x_out);
		outVars.put(yBoogie, y_out);
		
		Term transition = script.term("and", script.term("=", x_out, script.term("+", x_in, script.numeral("1"))),
				script.term(">", x_out, script.numeral("0")), script.term("=", y_out, script.term("+", y_in, script.numeral("1"))),
						script.term(">", y_out, script.numeral("0")));
		// transition: x_out = x_in + 1 && x_out > 0 && y_out = y_in + 1 && y_out > 0
		Set<Cube> cubeSet = ApproxPreimageCalculator.preimage(new FormulaAndLevelAnnotation(transition, levelAnnotation), script);
		TreeIC3.logger().debug("Cubes in the preimage:");
		TreeIC3.logger().debug(cubeSet);
		TreeIC3.logger().debug("");
	}
	
	
	
	public static void smtParserTests(Script script, Logger logger) {
		script.push(1);
		String text = "(forall ((var Int)) (= var var))";
		InputStreamReader input = new InputStreamReader(new ByteArrayInputStream(text.getBytes()));
		
		Term result = SMTParserInterface.parse(input, script);
		script.pop(1);
	}
	
	
	
	public static void substitutionTests(Script script) {
		script.push(1);
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Int");
		TermVariable x_in = theory.createTermVariable("xL0", intSort);
		TermVariable x_out = theory.createTermVariable("xL1", intSort);
		TermVariable x_out2 = theory.createTermVariable("xL2", intSort);
		TermVariable x_out3 = theory.createTermVariable("xL3", intSort);
		TermVariable x_in2 = theory.createTermVariable("xLminus1", intSort);
		BoogieVar x = new BoogieVar("x", null, null, false);
		String shift = SubstitutionManager.shiftVarname(x, 0, 0);
		assert(shift.equals(x_in.getName()));
		shift = SubstitutionManager.shiftVarname(x, 0, 1);
		assert(shift.equals(x_out.getName()));
		shift = SubstitutionManager.shiftVarname(x, 0, 2);
		assert(shift.equals(x_out2.getName()));
		shift = SubstitutionManager.shiftVarname(x, 0, 3);
		assert(shift.equals(x_out3.getName()));
		shift = SubstitutionManager.shiftVarname(x, 1, -1);
		assert(shift.equals(x_in.getName()));
		shift = SubstitutionManager.shiftVarname(x, 1, -2);
		assert(shift.equals(x_in2.getName()));
		Term testTerm = script.term("and", script.term("=", x_in, x_in), script.term("=", x_out, x_out));
		HashSet<TermVariable> allVars = new HashSet<TermVariable>();
		allVars.add(x_in);
		allVars.add(x_out);
		HashMap<BoogieVar, TermVariable> inVars = new HashMap<BoogieVar, TermVariable>();
		inVars.put(x, x_in);
		HashMap<BoogieVar, TermVariable> outVars = new HashMap<BoogieVar, TermVariable>();
		outVars.put(x, x_out);
		LevelAnnotations lvl = new LevelAnnotations(script, allVars, inVars, outVars);
		FormulaAndLevelAnnotation testTermAndLvl = new FormulaAndLevelAnnotation(testTerm, lvl);
		// testTerm: x_in = x_in and x_out = x_out
		FormulaAndLevelAnnotation shiftTermAndLvl = SubstitutionManager.substituteSpecificInToOut(script, testTermAndLvl, 0, false);
		assert(shiftTermAndLvl.getFormula().equals(testTermAndLvl.getFormula()));
		shiftTermAndLvl = SubstitutionManager.substituteSpecificInToOut(script, testTermAndLvl, 1, false);
		assert(shiftTermAndLvl.toString().equals(
			"(and (= ^1^xL1 ^1^xL1) (= ^2^xL2 ^2^xL2))"));
		shiftTermAndLvl = SubstitutionManager.substituteSpecificInToOut(script, testTermAndLvl, -1, false);
		assert(shiftTermAndLvl.toString().equals(
			"(and (= ^-1^xLminus1 ^-1^xLminus1) (= ^0^xL0 ^0^xL0))"));
		script.pop(1);
	}
	
	
	
	public static void nodeCoveringTests() {
		// TODO
	}
	
	
	
	public static void loopCfgNodesTests(CFGExplicitNode cfgRootNode) {
		Set<CFGExplicitNode> loopNodes = HelperMethods.determineLoopLocations(cfgRootNode);
		TreeIC3.logger().debug("List of detected cfg loop nodes:");
		for (CFGExplicitNode node : loopNodes) {
			TreeIC3.logger().debug(node.getPayload().getName());
		}
	}
	
	
	
	public static void freeVarsToConstTest(Script script) {
		script.push(1);
		Theory theory = script.term("true").getTheory();
		Sort intSort = script.sort("Bool");
		TermVariable a = theory.createTermVariable("a", intSort);
		TermVariable b = theory.createTermVariable("b", intSort);
		TermVariable c = theory.createTermVariable("c", intSort);
		Term first = script.term("and", a, b);
		Term second = script.term("and", b, c);
		ConstSubstResult result = SubstitutionManager.substituteFreeVarsToConst(script, first, null);
		ConstSubstResult result2 = SubstitutionManager.substituteFreeVarsToConst(script, second, result.getMap());
		script.pop(1);
	}
}
