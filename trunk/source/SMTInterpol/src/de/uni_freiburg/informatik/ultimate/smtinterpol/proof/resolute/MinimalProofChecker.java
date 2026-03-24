/*
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaLet;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * This proof checker checks compliance of SMTInterpol proofs with the minimal
 * proof format.
 *
 * @author Jochen Hoenicke
 */
public class MinimalProofChecker extends NonRecursive {

	/*
	 * The proof checker uses a non-recursive iteration through the proof tree. The
	 * main type in a proof tree is the sort {@literal @}Proof. Each term of this
	 * sort proves a formula and the main task of this code is to compute the proven
	 * formula. The whole proof term should prove the formula false.
	 *
	 * The main idea of this non-recursive algorithm is to push a proof walker for
	 * the {@literal @}Proof terms on the todo stack, which will push the proved
	 * clause of type ProofLiteral[] onto the result stack mStackResults. To handle
	 * functions like res, define-fun, etc. that take a {@literal @}Proof term as
	 * input, first a XYWalker for the function XY is pushed on the todo stack and
	 * then the ProofWalker for the {@literal @}Proof terms are pushed. The Walker
	 * will then call the corresponding walkXY function which checks the proved
	 * arguments, computes the final proved formula and pushes that on the result
	 * stack.
	 *
	 * Simple functions that don't take {@literal @}Proof arguments are handled
	 * directly by calling the walkXY function.
	 */

	/**
	 * The set of all asserted terms (collected from the script by calling
	 * getAssertions()). This is used to check the {@literal @}asserted rules.
	 */
	private Set<Term> mAssertions;

	/**
	 * The SMT script (mainly used to create terms).
	 */
	private final Script mSkript;
	/**
	 * The logger where errors are reported.
	 */
	private final LogProxy mLogger;

	/**
	 * The proof cache. It maps each converted proof to the clause it proves.
	 */
	private HashMap<Term, ProofLiteral[]> mCacheConv;

	/**
	 * Map from auxiliary function symbol to its definition. The auxiliary functions
	 * are functions defined in the proof term with define-fun.
	 */
	private final HashMap<FunctionSymbol, Term> mFunctionDefinitions;

	/**
	 * Map from function name to the expander for the expand axiom.
	 */
	private final HashMap<String, Expander> mInternalFunctionExpander;

	/**
	 * Map from axiom rule name to the implementation that computes the clause.
	 */
	private final HashMap<String, Axiom> mTheoryAxioms;

	/**
	 * The result stack. This contains the terms proved by the proof terms.
	 */
	private final Stack<ProofLiteral[]> mStackResults = new Stack<>();

	int mNumOracles, mNumAxioms, mNumResolutions, mNumAssertions, mNumDefineFun;

	/**
	 * Create a proof checker.
	 *
	 * @param script An SMT2 script.
	 * @param logger The logger where errors are reported.
	 */
	public MinimalProofChecker(final Script script, final LogProxy logger) {
		mSkript = script;
		mLogger = logger;
		mFunctionDefinitions = new HashMap<>();
		mInternalFunctionExpander = new HashMap<>();
		mTheoryAxioms = new HashMap<>();
		addTheoryDefinitions();
	}

	/**
	 * Check a proof for consistency. This reports errors on the logger.
	 *
	 * @param proof the proof to check.
	 * @return true, if no errors were found.
	 */
	public boolean check(final Term proof) {
		mNumOracles = mNumResolutions = mNumAxioms = mNumAssertions = mNumDefineFun = 0;

		final FormulaUnLet unletter = new FormulaUnLet();
		final Term[] assertions = mSkript.getAssertions();
		mAssertions = new HashSet<>(assertions.length);
		for (final Term ass : assertions) {
			mAssertions.add(unletter.transform(ass));
		}

		final ProofLiteral[] result = getProvedClause(unletter.unlet(proof));
		if (result != null && result.length > 0) {
			reportError("The proof did not yield a contradiction but %s", Arrays.asList(result));
			return false;
		}
		return true;
	}

	private Term createAnd(Term[] args) {
		final Theory theory = mSkript.getTheory();
		return args.length == 0 ? theory.mTrue : args.length == 1 ? args[0] : theory.term(SMTLIBConstants.AND, args);
	}

	public boolean checkModelProof(Term proof) {
		mNumOracles = mNumResolutions = mNumAxioms = mNumAssertions = mNumDefineFun = 0;
		mAssertions = Collections.emptySet();

		final FormulaUnLet unletter = new FormulaUnLet();
		proof = unletter.unlet(proof);

		final Map<FunctionSymbol, Term> funcDefs = new HashMap<FunctionSymbol, Term>();
		while (ProofRules.isRefineFun(proof)) {
			final AnnotatedTerm refineFunTerm = (AnnotatedTerm) proof;
			final Object[] annotValues = (Object[]) refineFunTerm.getAnnotations()[0].getValue();
			final FunctionSymbol func = (FunctionSymbol) annotValues[0];
			final Term def = (Term) annotValues[1];
			addRefineFun(funcDefs, func, def);
			proof = refineFunTerm.getSubterm();
		}

		final ProofLiteral[] result = getProvedClause(funcDefs, proof);
		Term destFormula = createAnd(mSkript.getAssertions());
		destFormula = unletter.transform(destFormula);
		if (result == null || result.length != 1 || !result[0].getPolarity()
				|| result[0].getAtom() != destFormula) {
			reportError("The proof did not prove the assertions but %s", Arrays.asList(result));
			return false;
		}
		return true;
	}

	private void checkFunctionConsistency(FunctionSymbol func, TermVariable[] variables, Term definition) {
		if (variables.length != func.getParameterSorts().length) {
			throw new AssertionError("Parameter count mismatch");
		}
		if (func.getDefinition() != null
				&& (func.getDefinition() != definition || !Arrays.equals(func.getDefinitionVars(), variables))) {
			throw new AssertionError("Inconsistent function definition.");
		}
	}

	public void addRefineFun(Map<FunctionSymbol, Term> funcDefs, FunctionSymbol func, Term def) {
		if (func.isIntern()) {
			// TODO: check that function definition is refinement.
			// i.e. divison is only refined for division by 0,
			// selector is only refined for different constructor,
			// @diff is only refined in such a way that it returns an element where the
			// arrays differ.
		}
		if (def instanceof LambdaTerm) {
			final LambdaTerm lambda = (LambdaTerm) def;
			checkFunctionConsistency(func, lambda.getVariables(), lambda.getSubterm());
		} else {
			checkFunctionConsistency(func, new TermVariable[0], def);
		}
		if (funcDefs.containsKey(func)) {
			throw new AssertionError("Double function definition.");
		}
		funcDefs.put(func, def);
	}

	private static Term expandDefinition(Term definition, TermVariable[] vars, Term[] params) {
		return new FormulaUnLet().unlet(definition.getTheory().let(vars, params, definition));
	}

	public Term expandFunctionSymbol(FunctionSymbol func, Term[] params) {
		if (func.getDefinition() != null) {
			return expandDefinition(func.getDefinition(), func.getDefinitionVars(), params);
		} else if (func.isIntern() && mInternalFunctionExpander.containsKey(func.getName())) {
			final Expander expander = mInternalFunctionExpander.get(func.getName());
			return expander.expand(func, params);
		} else if (mFunctionDefinitions.containsKey(func)) {
			final Term definition = mFunctionDefinitions.get(func);
			if (definition instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) definition;
				return expandDefinition(lambda.getSubterm(), lambda.getVariables(), params);
			} else {
				assert params.length == 0;
				return definition;
			}
		} else {
			throw new AssertionError();
		}
	}

	void registerExpand(String funcName, Expander expander) {
		mInternalFunctionExpander.put(funcName, expander);
	}

	void registerAxiom(String ruleName, Axiom axiom) {
		mTheoryAxioms.put(ruleName, axiom);
	}

	private void addTheoryDefinitions() {
		final Theory theory = mSkript.getTheory();
		final Logics logic = theory.getLogic();
		CoreRules.registerRules(this);
		if (logic.isArithmetic() || logic.isBitVector()) {
			ArithmeticRules.registerRules(this);
		}
		if (logic.isBitVector()) {
			BitvectorRules.registerRules(this);
		}
		if (logic.isArray()) {
			ArrayRules.registerRules(this);
		}
		if (logic.isDatatype()) {
			DataTypeRules.registerRules(this);
		}
	}

	public int getNumberOfHoles() {
		return mNumOracles;
	}

	public int getNumberOfResolutions() {
		return mNumResolutions;
	}

	public int getNumberOfAxioms() {
		return mNumAxioms;
	}

	public int getNumberOfAssertions() {
		return mNumAssertions;
	}

	public int getNumberOfDefineFun() {
		return mNumDefineFun;
	}

	/**
	 * Check a proof for consistency and compute the proved clause. This prints
	 * warnings for missing pivot literals.
	 *
	 * @param proof the proof to check.
	 * @return the proved clause.
	 */
	public ProofLiteral[] getProvedClause(final Term proof) {
		return getProvedClause(null, proof);
	}

	/**
	 * Check a proof for consistency and compute the proved clause. This prints
	 * warnings for missing pivot literals.
	 *
	 * @param funcDefs the function definitions (for expand rule)
	 * @param proof    the proof to check.
	 * @return the proved clause.
	 */
	public ProofLiteral[] getProvedClause(final Map<FunctionSymbol, Term> funcDefs, final Term proof) {
		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		if (funcDefs != null) {
			for (final Map.Entry<FunctionSymbol, Term> funcDef : funcDefs.entrySet()) {
				final FunctionSymbol func = funcDef.getKey();
				final Term def = funcDef.getValue();
				if (func.getDefinition() != null) {
					// check that definitions equal
					if (func.getDefinitionVars().length == 0) {
						if (func.getDefinition() != def) {
							throw new AssertionError("Inconsistent function definition.");
						}
					} else {
						final LambdaTerm lambda = (LambdaTerm) def;
						if (func.getDefinition() != lambda.getSubterm()
								|| !Arrays.equals(func.getDefinitionVars(), lambda.getVariables())) {
							throw new AssertionError("Inconsistent function definition.");
						}
					}
				}
				mFunctionDefinitions.put(func, def);
			}
		}
		run(new ProofWalker(proof));
		assert (mStackResults.size() == 1);
		if (funcDefs != null) {
			for (final FunctionSymbol func : funcDefs.keySet()) {
				mFunctionDefinitions.remove(func);
			}
		}
		// clear state
		mCacheConv = null;

		return stackPop();
	}

	private void reportError(final String msg, final Object... params) {
		mLogger.error(msg, params);
	}

	private void reportWarning(final String msg, final Object... params) {
		mLogger.warn(msg, params);
	}

	/**
	 * The proof walker. This takes a proof term and pushes the proven formula on
	 * the result stack. It also checks the proof cache to prevent running over the
	 * same term twice.
	 *
	 * @param proofTerm The proof term. Its sort must be {@literal @}Proof.
	 */
	void walk(Term proofTerm) {
		while (proofTerm instanceof AnnotatedTerm && !ProofRules.isAxiom(proofTerm)
				&& !ProofRules.isDefineFun(proofTerm)) {
			if (ProofRules.isRefineFun(proofTerm)) {
				mLogger.warn("Ignoring refine-fun in the middle of the proof term", proofTerm);
			}
			proofTerm = ((AnnotatedTerm) proofTerm).getSubterm();
		}
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			mStackResults.push(mCacheConv.get(proofTerm));
			return;
		}
		if (ProofRules.isDefineFun(proofTerm)) {
			new DefineFunWalker((AnnotatedTerm) proofTerm).enqueue(this);
		} else if (ProofRules.isAxiom(proofTerm)) {
			stackPush(computeAxiom(proofTerm), proofTerm);
		} else if (ProofRules.isProofRule(ProofRules.RES, proofTerm)) {
			new ResolutionWalker((ApplicationTerm) proofTerm).enqueue(this);
		} else {
			stackPush(checkAssert(proofTerm), proofTerm);
		}
	}

	/**
	 * Handle the resolution rule. The stack should contain the converted input
	 * clauses.
	 *
	 * @param resApp The <code>{@literal @}res</code> application from the original
	 *               proof.
	 */
	ProofLiteral[] walkResolution(final ApplicationTerm resApp, final ProofLiteral[] posClause,
			final ProofLiteral[] negClause) {
		mNumResolutions++;

		/*
		 * allDisjuncts is the currently computed resolution result.
		 */
		final HashSet<ProofLiteral> allDisjuncts = new HashSet<>();

		final Term pivot = resApp.getParameters()[0];
		final ProofLiteral posPivot = new ProofLiteral(pivot, true);
		final ProofLiteral negPivot = new ProofLiteral(pivot, false);

		/* Add non-pivot disjuncts of the first clause. */
		boolean pivotFound = false;
		for (final ProofLiteral lit : posClause) {
			if (lit.equals(posPivot)) {
				pivotFound = true;
			} else {
				allDisjuncts.add(lit);
			}
		}

		/* Remove the pivot from allDisjuncts */
		if (!pivotFound) {
			reportWarning("Could not find pivot %s in %s", posPivot, Arrays.asList(posClause));
		}

		pivotFound = false;
		for (final ProofLiteral lit : negClause) {
			if (lit.equals(negPivot)) {
				pivotFound = true;
			} else {
				allDisjuncts.add(lit);
			}
		}

		if (!pivotFound) {
			reportWarning("Could not find pivot %s in %s", negPivot, Arrays.asList(negClause));
		}
		return allDisjuncts.toArray(new ProofLiteral[allDisjuncts.size()]);
	}

	/* === Auxiliary functions === */

	void stackPush(final ProofLiteral[] pushClause, final Term keyTerm) {
		mCacheConv.put(keyTerm, pushClause);
		mStackResults.push(pushClause);
	}

	ProofLiteral[] stackPop() {
		return mStackResults.pop();
	}

	public ProofLiteral[] computeAxiom(final Term axiom) {
		mNumAxioms++;
		final Theory theory = axiom.getTheory();
		assert ProofRules.isAxiom(axiom);
		final Annotation[] annots = ((AnnotatedTerm) axiom).getAnnotations();

		if (annots[0].getKey() == ProofRules.ORACLE) {
			mNumOracles++;
			mNumAxioms--;
			reportWarning("Used oracle: %s", Arrays.asList(annots).subList(1, annots.length));
			mLogger.info("Full oracle: %s", new Object() {
				@Override
				public String toString() {
					final Term letted = new FormulaLet().let(axiom);
					final StringBuilder sb = new StringBuilder();
					ProofRules.printProof(sb, letted);
					return sb.toString();
				}
			});
			// convert to clause (and remove multiple occurrences)
			final ProofLiteral[] lits = ProofRules.proofLiteralsFromAnnotation((Object[]) annots[0].getValue());
			final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>(Arrays.asList(lits));
			return clause.toArray(new ProofLiteral[clause.size()]);
		}

		assert annots.length == 1;
		final Axiom axiomGenerator = mTheoryAxioms.get(annots[0].getKey());
		if (axiomGenerator == null) {
			reportError("Unknown axiom %s", axiom);
			return getTrueClause(axiom.getTheory());
		}
		final Object[] params = (Object[]) annots[0].getValue();
		try {
			return axiomGenerator.computeAxiom(this, theory, params);
		} catch (final RuntimeException ex) {
			return reportViolatedSideCondition(axiom);
		}
	}

	private ProofLiteral[] reportViolatedSideCondition(final Term axiom) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Side-condition violated in ");
		ProofRules.printProof(sb, axiom);
		reportError(sb.toString());
		return getTrueClause(axiom.getTheory());
	}

	/**
	 * Dummy clause (+ true) that is created for axioms whose side-condition is not
	 * valid.
	 *
	 * @return a dummy clause that doesn't proof anything (but is valid).
	 */
	private ProofLiteral[] getTrueClause(final Theory theory) {
		return new ProofLiteral[] { new ProofLiteral(theory.mTrue, true) };
	}

	public ProofLiteral[] checkAssert(final Term axiom) {
		mNumAssertions++;
		final ApplicationTerm appTerm = (ApplicationTerm) axiom;
		final Term[] params = appTerm.getParameters();
		assert appTerm.getFunction().getName() == ProofRules.PREFIX + ProofRules.ASSUME;
		assert params.length == 1;
		if (!mAssertions.contains(params[0])) {
			reportError("Unknown assumption: %s", params[0]);
			return getTrueClause(axiom.getTheory());
		}
		return new ProofLiteral[] { new ProofLiteral(params[0], true) };
	}

	/**
	 * The main proof walker that handles a term of sort {@literal @}Proof. It just
	 * calls the walk function.
	 */
	static class ProofWalker implements Walker {
		final Term mTerm;

		public ProofWalker(final Term term) {
			assert term.getSort().getName().equals(ProofRules.PREFIX + ProofRules.PROOF);
			mTerm = term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((MinimalProofChecker) engine).walk(mTerm);
		}
	}

	/**
	 * The proof walker that handles define-fun.
	 */
	static class DefineFunWalker implements Walker {
		final AnnotatedTerm mProof;

		public DefineFunWalker(final AnnotatedTerm term) {
			mProof = term;
		}

		public void enqueue(final MinimalProofChecker engine) {
			engine.mNumDefineFun++;
			final Object[] annotValues = (Object[]) mProof.getAnnotations()[0].getValue();
			final FunctionSymbol func = (FunctionSymbol) annotValues[0];
			final Term def = (Term) annotValues[1];
			if (def instanceof LambdaTerm) {
				final LambdaTerm lambda = (LambdaTerm) def;
				engine.checkFunctionConsistency(func, lambda.getVariables(), lambda.getSubterm());
			} else {
				engine.checkFunctionConsistency(func, new TermVariable[0], def);
			}
			if (engine.mFunctionDefinitions.containsKey(func)) {
				throw new AssertionError("Double function definition.");
			}
			engine.mFunctionDefinitions.put(func, def);
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(mProof.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive parent) {
			final MinimalProofChecker engine = (MinimalProofChecker) parent;
			final Object[] annotValues = (Object[]) mProof.getAnnotations()[0].getValue();
			final FunctionSymbol func = (FunctionSymbol) annotValues[0];
			engine.mFunctionDefinitions.remove(func);
		}
	}

	/**
	 * The proof walker that handles the resolution rule after its arguments are
	 * converted. It just calls the walkResolution function.
	 */
	static class ResolutionWalker implements Walker {
		final ApplicationTerm mTerm;

		public ResolutionWalker(final ApplicationTerm term) {
			mTerm = term;
		}

		public void enqueue(final MinimalProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(params[2]));
			engine.enqueueWalker(new ProofWalker(params[1]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final MinimalProofChecker checker = (MinimalProofChecker) engine;
			final ProofLiteral[] negClause = checker.stackPop();
			final ProofLiteral[] posClause = checker.stackPop();
			checker.stackPush(checker.walkResolution(mTerm, posClause, negClause), mTerm);
		}
	}

	static interface Expander {
		public Term expand(FunctionSymbol f, Term[] args);
	}

	static interface Axiom {
		public ProofLiteral[] computeAxiom(MinimalProofChecker checker, Theory theory, Object[] params);
	}
}
