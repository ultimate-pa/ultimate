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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;

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
	 * term of type Bool onto the result stack mStackResults. To handle functions
	 * like {@literal @}eq, {@literal @}cong, {@literal @}trans that take a
	 * {@literal @}Proof term as input, first a XYWalker the function XY is pushed
	 * on the todo stack and then the ProofWalker for the {@literal @}Proof terms
	 * are pushed. The Walker will then call the corresponding walkXY function which
	 * checks the proved arguments, computes the final proved formula and pushes
	 * that on the result stack.
	 *
	 * Simple functions that don't take {@literal @}Proof arguments are handled
	 * directly by calling the walkXY function.
	 */

	/**
	 * The set of all asserted terms (collected from the script by calling
	 * getAssertions()). This is used to check the {@literal @}asserted rules.
	 */
	HashSet<Term> mAssertions;

	/**
	 * The SMT script (mainly used to create terms).
	 */
	Script mSkript;
	/**
	 * The logger where errors are reported.
	 */
	LogProxy mLogger;
	/**
	 * The ProofRules object.
	 */
	ProofRules mProofRules;

	/**
	 * The proof cache. It maps each converted proof to the clause it proves.
	 */
	HashMap<Term, ProofLiteral[]> mCacheConv;

	/**
	 * Map from auxiliary function symbol to its definition. The auxiliary
	 * functions are functions defined in the proof term with define-fun.
	 */
	HashMap<FunctionSymbol, LambdaTerm> mFunctionDefinitions;

	/**
	 * The result stack. This contains the terms proved by the proof terms.
	 */
	Stack<ProofLiteral[]> mStackResults = new Stack<>();

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
		mProofRules = new ProofRules(script.getTheory());

		final FormulaUnLet unletter = new FormulaUnLet();
		final Term[] assertions = mSkript.getAssertions();
		mAssertions = new HashSet<>(assertions.length);
		for (final Term ass : assertions) {
			mAssertions.add(unletter.transform(ass));
		}
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
		final ProofLiteral[] result = getProvedClause(unletter.unlet(proof));
		if (result != null && result.length > 0) {
			reportError("The proof did not yield a contradiction but %s", Arrays.asList(result));
			return false;
		}
		return true;
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
	public ProofLiteral[] getProvedClause(final Map<FunctionSymbol, LambdaTerm> funcDefs, final Term proof) {
		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		mFunctionDefinitions = new HashMap<>();
		if (funcDefs != null) {
			for (final Map.Entry<FunctionSymbol, LambdaTerm> funcDef : funcDefs.entrySet()) {
				final FunctionSymbol func = funcDef.getKey();
				final LambdaTerm def = funcDef.getValue();
				if (!func.isIntern() && func.getDefinition() != null && (func.getDefinition() != def.getSubterm()
						|| !Arrays.equals(func.getDefinitionVars(), def.getVariables()))) {
					throw new AssertionError("Inconsistent function definition.");
				}
				mFunctionDefinitions.put(func, def);
			}
		}
		run(new ProofWalker(proof));
		assert (mStackResults.size() == 1);
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
			proofTerm = ((AnnotatedTerm) proofTerm).getSubterm();
		}
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			stackPush(mCacheConv.get(proofTerm), proofTerm);
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
		switch (annots[0].getKey()) {
		case ":" + ProofRules.ORACLE: {
			mNumOracles++;
			mNumAxioms--;
			reportWarning("Used oracle: %s", axiom);
			// convert to clause (and remove multiple occurrences)
			final ProofLiteral[] lits = ProofRules.proofLiteralsFromAnnotation((Object[]) annots[0].getValue());
			final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>(Arrays.asList(lits));
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.TRUEI: {
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.TRUE), true) };
		}
		case ":" + ProofRules.FALSEE: {
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.FALSE), false) };
		}
		case ":" + ProofRules.NOTI: {
			assert annots.length == 1;
			final ApplicationTerm notTerm = (ApplicationTerm) annots[0].getValue();
			if (!notTerm.getFunction().isIntern() || !notTerm.getFunction().getName().equals(SMTLIBConstants.NOT)) {
				reportError("Expected not application");
				return getTrueClause(notTerm.getTheory());
			}
			// (not t), t
			return new ProofLiteral[] { new ProofLiteral(notTerm, true),
					new ProofLiteral(notTerm.getParameters()[0], true) };
		}
		case ":" + ProofRules.NOTE: {
			assert annots.length == 1;
			final ApplicationTerm notTerm = (ApplicationTerm) annots[0].getValue();
			if (!notTerm.getFunction().isIntern() || !notTerm.getFunction().getName().equals(SMTLIBConstants.NOT)) {
				reportError("Expected not application");
				return getTrueClause(notTerm.getTheory());
			}
			// ~(not t), ~t
			return new ProofLiteral[] { new ProofLiteral(notTerm, false),
					new ProofLiteral(notTerm.getParameters()[0], false) };
		}
		case ":" + ProofRules.ORI: {
			assert annots.length == 2;
			final ApplicationTerm orTerm = (ApplicationTerm) annots[0].getValue();
			if (!orTerm.getFunction().isIntern() || !orTerm.getFunction().getName().equals(SMTLIBConstants.OR)) {
				reportError("Expected or application");
				return getTrueClause(orTerm.getTheory());
			}
			final Term[] params = orTerm.getParameters();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final int pos = (Integer) annots[1].getValue();
			assert pos >= 0 && pos < params.length;

			// (or t1 ... tn), ~tpos
			return new ProofLiteral[] { new ProofLiteral(orTerm, true),
					new ProofLiteral(params[pos], false) };
		}
		case ":" + ProofRules.ORE: {
			assert annots.length == 1;
			final ApplicationTerm orTerm = (ApplicationTerm) annots[0].getValue();
			if (!orTerm.getFunction().isIntern() || !orTerm.getFunction().getName().equals(SMTLIBConstants.OR)) {
				reportError("Expected or application");
				return getTrueClause(orTerm.getTheory());
			}
			final Term[] params = orTerm.getParameters();

			// ~(or t1 ... tn), t1, ..., tn
			final HashSet<ProofLiteral> clause = new HashSet<>();
			clause.add(new ProofLiteral(orTerm, false));
			for (final Term param : params) {
				clause.add(new ProofLiteral(param, true));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.ANDI: {
			assert annots.length == 1;
			final ApplicationTerm andTerm = (ApplicationTerm) annots[0].getValue();
			if (!andTerm.getFunction().isIntern() || !andTerm.getFunction().getName().equals(SMTLIBConstants.AND)) {
				reportError("Expected and application");
				return getTrueClause(andTerm.getTheory());
			}
			final Term[] params = andTerm.getParameters();

			// (and t1 ... tn), ~t1, ..., ~tn
			final HashSet<ProofLiteral> clause = new HashSet<>();
			clause.add(new ProofLiteral(andTerm, true));
			for (final Term param : params) {
				clause.add(new ProofLiteral(param, false));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.ANDE: {
			assert annots.length == 2;
			final ApplicationTerm andTerm = (ApplicationTerm) annots[0].getValue();
			if (!andTerm.getFunction().isIntern() || !andTerm.getFunction().getName().equals(SMTLIBConstants.AND)) {
				reportError("Expected and application");
				return getTrueClause(andTerm.getTheory());
			}
			final Term[] params = andTerm.getParameters();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final int pos = (Integer) annots[1].getValue();
			assert pos >= 0 && pos < params.length;

			// ~(and t1 ... tn), tpos
			return new ProofLiteral[] { new ProofLiteral(andTerm, false),
					new ProofLiteral(params[pos], true) };
		}
		case ":" + ProofRules.IMPI: {
			assert annots.length == 2;
			final ApplicationTerm impTerm = (ApplicationTerm) annots[0].getValue();
			if (!impTerm.getFunction().isIntern() || !impTerm.getFunction().getName().equals(SMTLIBConstants.IMPLIES)) {
				reportError("Expected => application");
				return getTrueClause(impTerm.getTheory());
			}
			final Term[] params = impTerm.getParameters();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final int pos = (Integer) annots[1].getValue();
			assert pos >= 0 && pos < params.length;

			// (=> t1 ... tn), tpos (~tpos if pos == n)
			return new ProofLiteral[] { new ProofLiteral(impTerm, true),
					new ProofLiteral(params[pos], pos < params.length - 1) };
		}
		case ":" + ProofRules.IMPE: {
			assert annots.length == 1;
			final ApplicationTerm impTerm = (ApplicationTerm) annots[0].getValue();
			if (!impTerm.getFunction().isIntern() || !impTerm.getFunction().getName().equals(SMTLIBConstants.IMPLIES)) {
				reportError("Expected => application");
				return getTrueClause(impTerm.getTheory());
			}
			final Term[] params = impTerm.getParameters();

			// ~(=> t1 ... tn), ~t1, ..., ~tn-1, tn
			final HashSet<ProofLiteral> clause = new HashSet<>();
			clause.add(new ProofLiteral(impTerm, false));
			for (int i = 0; i < params.length; i++) {
				clause.add(new ProofLiteral(params[i], i == params.length - 1));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.IFFI1: {
			assert annots.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) annots[0].getValue();
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// (= t1 t2), t1, t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, true),
					new ProofLiteral(params[0], true), new ProofLiteral(params[1], true) };
		}
		case ":" + ProofRules.IFFI2: {
			assert annots.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) annots[0].getValue();
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// (= t1 t2), ~t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, true),
					new ProofLiteral(params[0], false), new ProofLiteral(params[1], false) };
		}
		case ":" + ProofRules.IFFE1: {
			assert annots.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) annots[0].getValue();
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// ~(= t1 t2), t1, ~t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, false),
					new ProofLiteral(params[0], true), new ProofLiteral(params[1], false) };
		}
		case ":" + ProofRules.IFFE2: {
			assert annots.length == 1;
			final ApplicationTerm iffTerm = (ApplicationTerm) annots[0].getValue();
			if (!iffTerm.getFunction().isIntern() || !iffTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(iffTerm.getTheory());
			}
			final Term[] params = iffTerm.getParameters();
			if (params.length != 2 || params[0].getSort().getName() != SMTLIBConstants.BOOL) {
				return reportViolatedSideCondition(axiom);
			}

			// ~(= t1 t2), ~t1, t2
			return new ProofLiteral[] { new ProofLiteral(iffTerm, false),
					new ProofLiteral(params[0], false), new ProofLiteral(params[1], true) };
		}
		case ":" + ProofRules.XORI: {
			assert annots.length == 1;
			final Term[][] xorLists = (Term[][]) annots[0].getValue();
			assert xorLists.length == 3;
			if (!ProofRules.checkXorParams(xorLists)) {
				return reportViolatedSideCondition(axiom);
			}
			// (xor set0), (xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				final Term term = xorLists[i].length == 1 ? xorLists[i][0]
						: theory.term(SMTLIBConstants.XOR, xorLists[i]);
				assert term != null;
				clause[i] = new ProofLiteral(term, i < 2);
			}
			return clause;
		}
		case ":" + ProofRules.XORE: {
			assert annots.length == 1;
			final Term[][] xorLists = (Term[][]) annots[0].getValue();
			assert xorLists.length == 3;
			if (!ProofRules.checkXorParams(xorLists)) {
				return reportViolatedSideCondition(axiom);
			}
			// ~(xor set0), ~(xor set1), ~(xor set2)
			final ProofLiteral[] clause = new ProofLiteral[3];
			for (int i = 0; i < 3; i++) {
				final Term term = xorLists[i].length == 1 ? xorLists[i][0]
						: theory.term(SMTLIBConstants.XOR, xorLists[i]);
				assert term != null;
				clause[i] = new ProofLiteral(term, false);
			}
			return clause;
		}
		case ":" + ProofRules.EQI: {
			assert annots.length == 1;
			final ApplicationTerm eqTerm = (ApplicationTerm) annots[0].getValue();
			if (!eqTerm.getFunction().isIntern() || !eqTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(eqTerm.getTheory());
			}
			final Term[] params = eqTerm.getParameters();

			// (= t1 ... tn), ~(= t1 t2), ~(tn-1 tn)
			final ProofLiteral[] clause = new ProofLiteral[params.length];
			clause[0] = new ProofLiteral(eqTerm, true);
			for (int i = 0; i < params.length - 1; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[i + 1]), false);
			}
			return clause;
		}
		case ":" + ProofRules.EQE: {
			assert annots.length == 2;
			final ApplicationTerm eqTerm = (ApplicationTerm) annots[0].getValue();
			if (!eqTerm.getFunction().isIntern() || !eqTerm.getFunction().getName().equals(SMTLIBConstants.EQUALS)) {
				reportError("Expected = application");
				return getTrueClause(eqTerm.getTheory());
			}
			final Term[] params = eqTerm.getParameters();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final Integer[] positions = (Integer[]) annots[1].getValue();
			assert positions.length == 2;
			final int pos0 = positions[0];
			final int pos1 = positions[1];
			assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

			// ~(= t1 ... tn), (= ti tj)
			return new ProofLiteral[] { new ProofLiteral(eqTerm, false),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[pos0], params[pos1]), true) };
		}
		case ":" + ProofRules.DISTINCTI: {
			assert annots.length == 1;
			final ApplicationTerm distinctTerm = (ApplicationTerm) annots[0].getValue();
			if (!distinctTerm.getFunction().isIntern()
					|| !distinctTerm.getFunction().getName().equals(SMTLIBConstants.DISTINCT)) {
				reportError("Expected distinct application");
				return getTrueClause(distinctTerm.getTheory());
			}
			final Term[] params = distinctTerm.getParameters();
			final int len = params.length;

			// (distinct t1 ... tn), (= t1 t2),...
			final ProofLiteral[] clause = new ProofLiteral[1 + len * (len - 1) / 2];
			clause[0] = new ProofLiteral(distinctTerm, true);
			int pos = 1;
			for (int i = 0; i < len - 1; i++) {
				for (int j = i + 1; j < len; j++) {
					clause[pos++] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[j]), true);
				}
			}
			assert pos == clause.length;
			return clause;
		}
		case ":" + ProofRules.DISTINCTE: {
			assert annots.length == 2;
			final ApplicationTerm distinctTerm = (ApplicationTerm) annots[0].getValue();
			if (!distinctTerm.getFunction().isIntern()
					|| !distinctTerm.getFunction().getName().equals(SMTLIBConstants.DISTINCT)) {
				reportError("Expected distinct application");
				return getTrueClause(distinctTerm.getTheory());
			}
			final Term[] params = distinctTerm.getParameters();
			assert annots[1].getKey().equals(ProofRules.ANNOT_POS);
			final Integer[] positions = (Integer[]) annots[1].getValue();
			assert positions.length == 2;
			final int pos0 = positions[0];
			final int pos1 = positions[1];
			assert 0 <= pos0 && pos0 < params.length && 0 <= pos1 && pos1 < params.length;

			// ~(distinct t1 ... tn), ~(= ti tj)
			return new ProofLiteral[] { new ProofLiteral(distinctTerm, false),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[pos0], params[pos1]), false) };
		}
		case ":" + ProofRules.ITE1: {
			assert annots.length == 1;
			final ApplicationTerm iteTerm = (ApplicationTerm) annots[0].getValue();
			if (!iteTerm.getFunction().isIntern() || !iteTerm.getFunction().getName().equals(SMTLIBConstants.ITE)) {
				reportError("Expected ite application");
				return getTrueClause(iteTerm.getTheory());
			}
			final Term[] params = iteTerm.getParameters();
			assert params.length == 3;

			// (= (ite c t e) t), ~c
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, iteTerm, params[1]), true),
					new ProofLiteral(params[0], false) };
		}
		case ":" + ProofRules.ITE2: {
			assert annots.length == 1;
			final ApplicationTerm iteTerm = (ApplicationTerm) annots[0].getValue();
			if (!iteTerm.getFunction().isIntern() || !iteTerm.getFunction().getName().equals(SMTLIBConstants.ITE)) {
				reportError("Expected ite application");
				return getTrueClause(iteTerm.getTheory());
			}
			final Term[] params = iteTerm.getParameters();
			assert params.length == 3;

			// (= (ite c t e) e), c
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, iteTerm, params[2]), true),
					new ProofLiteral(params[0], true) };
		}
		case ":" + ProofRules.DELANNOT: {
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 2;
			final Term subterm = (Term) params[0];
			final Annotation[] subAnnots = ProofRules.convertSExprToAnnotation((Object[]) params[1]);
			final Term annotTerm = theory.annotatedTerm(subAnnots, subterm);

			// (= (! t :...) t)
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, annotTerm, subterm), true) };
		}
		case ":" + ProofRules.REFL: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;

			// (= a a)
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[0]), true) };
		}
		case ":" + ProofRules.SYMM: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;

			// (= a0 a1), ~(= a1 a0)
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[1], params[0]), false) };
		}
		case ":" + ProofRules.TRANS: {
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length > 2;
			final int len = params.length;

			// (= a0 alen-1), ~(= a0 a1), ..., ~(= alen-2 alen-1)
			final ProofLiteral[] clause = new ProofLiteral[len];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[len - 1]), true);
			for (int i = 0; i < len - 1; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[i], params[i + 1]), false);
			}
			return clause;
		}
		case ":" + ProofRules.CONG: {
			assert annots.length == 1;
			final Object[] congArgs = (Object[]) annots[0].getValue();
			assert congArgs.length == 3;
			final FunctionSymbol func = (FunctionSymbol) congArgs[0];
			final Term[] params0 = (Term[]) congArgs[1];
			final Term[] params1 = (Term[]) congArgs[2];
			assert params0.length == params1.length;
			final Term app0 = theory.term(func, params0);
			final Term app1 = theory.term(func, params1);

			// (= (f a0...an) (f b0... bn)), ~(= a0 b0), ..., ~(= an bn)
			final ProofLiteral[] clause = new ProofLiteral[params0.length + 1];
			clause[0] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, app0, app1), true);
			for (int i = 0; i < params0.length; i++) {
				clause[i + 1] = new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params0[i], params1[i]), false);
			}
			return clause;
		}
		case ":" + ProofRules.EXPAND: {
			assert annots.length == 1;
			final Object[] expandArgs = (Object[]) annots[0].getValue();
			assert expandArgs.length == 2;
			final FunctionSymbol func = (FunctionSymbol) expandArgs[0];
			final Term[] params = (Term[]) expandArgs[1];
			final Term app = theory.term(func, params);
			Term rhs;
			if (mFunctionDefinitions.containsKey(func)) {
				final LambdaTerm lambda = mFunctionDefinitions.get(func);
				rhs = theory.let(lambda.getVariables(), params, lambda.getSubterm());
				rhs = new FormulaUnLet().unlet(rhs);
			} else if (func.getDefinition() != null) {
				rhs = theory.let(func.getDefinitionVars(), params, func.getDefinition());
				rhs = new FormulaUnLet().unlet(rhs);
			} else if (func.isLeftAssoc() && params.length > 2) {
				rhs = params[0];
				for (int i = 1; i < params.length; i++) {
					rhs = theory.term(func, rhs, params[i]);
				}
			} else if (func.isRightAssoc() && params.length > 2) {
				rhs = params[params.length - 1];
				for (int i = params.length - 2; i >= 0; i--) {
					rhs = theory.term(func, params[i], rhs);
				}
			} else if (func.isChainable() && params.length > 2) {
				final Term[] chain = new Term[params.length - 1];
				for (int i = 0; i < chain.length; i++) {
					chain[i] = theory.term(func, params[i], params[i + 1]);
				}
				rhs = theory.term("and", chain);
			} else {
				throw new AssertionError();
			}
			return new ProofLiteral[] { new ProofLiteral(theory.term("=", app, rhs), true) };
		}
		case ":" + ProofRules.FORALLI:
		case ":" + ProofRules.EXISTSE: {
			assert annots.length == 1;
			final boolean isForall = annots[0].getKey().equals(":" + ProofRules.FORALLI);
			final QuantifiedFormula quant = (QuantifiedFormula) annots[0].getValue();
			if (quant.getQuantifier() != (isForall ? QuantifiedFormula.FORALL : QuantifiedFormula.EXISTS)) {
				reportError("Quantifier of wrong type");
				return getTrueClause(theory);
			}
			final TermVariable[] termVars = quant.getVariables();
			final Term[] skolemTerms = new ProofRules(theory).getSkolemVars(termVars, quant.getSubformula(), isForall);
			final Term letted = theory.let(termVars, skolemTerms, quant.getSubformula());

			// (forall (vars) F), ~(let skolem F)
			// ~(exists (vars) F), (let skolem F)
			return new ProofLiteral[] { new ProofLiteral(quant, isForall),
					new ProofLiteral(new FormulaUnLet().unlet(letted), !isForall) };
		}
		case ":" + ProofRules.FORALLE:
		case ":" + ProofRules.EXISTSI: {
			assert annots.length == 2;
			final boolean isForall = annots[0].getKey().equals(":" + ProofRules.FORALLE);
			final QuantifiedFormula quant = (QuantifiedFormula) annots[0].getValue();
			if (quant.getQuantifier() != (isForall ? QuantifiedFormula.FORALL : QuantifiedFormula.EXISTS)) {
				reportError("Quantifier of wrong type");
				return getTrueClause(theory);
			}
			final TermVariable[] termVars = quant.getVariables();
			assert annots[1].getKey() == ProofRules.ANNOT_VALUES;
			final Term[] values = (Term[]) annots[1].getValue();
			final Term letted = theory.let(termVars, values, quant.getSubformula());

			// ~(forall (vars) F), (let values F)
			// (exists (vars) F), ~(let values F)
			return new ProofLiteral[] { new ProofLiteral(quant, !isForall),
					new ProofLiteral(new FormulaUnLet().unlet(letted), isForall) };
		}
		case ":" + ProofRules.GTDEF: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			if (params.length != 2) {
				throw new AssertionError();
			}
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, theory.term(SMTLIBConstants.GT, params),
							theory.term(SMTLIBConstants.LT, params[1], params[0])), true) };
		}
		case ":" + ProofRules.GEQDEF: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			if (params.length != 2) {
				throw new AssertionError();
			}
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, theory.term(SMTLIBConstants.GEQ, params),
							theory.term(SMTLIBConstants.LEQ, params[1], params[0])), true) };
		}
		case ":" + ProofRules.TRICHOTOMY: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			if (params.length != 2) {
				throw new AssertionError();
			}
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LT, params), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params), true),
					new ProofLiteral(theory.term(SMTLIBConstants.LT, params[1], params[0]), true) };
		}
		case ":" + ProofRules.TOTAL: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, params[0], params[1]), true),
					new ProofLiteral(theory.term(SMTLIBConstants.LT, params[1], params[0]), true) };
		}
		case ":" + ProofRules.TOTALINT: {
			if (!theory.getLogic().hasIntegers()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 2;
			final Term x = (Term) params[0];
			final BigInteger c = (BigInteger) params[1];
			if (!x.getSort().getName().equals(SMTLIBConstants.INT)) {
				return reportViolatedSideCondition(axiom);
			}
			final Rational cAsRational = Rational.valueOf(c, BigInteger.ONE);
			final Term cTerm = cAsRational.toTerm(x.getSort());
			final Term cPlusOne = cAsRational.add(Rational.ONE).toTerm(x.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, x, cTerm), true),
					new ProofLiteral(theory.term(SMTLIBConstants.LEQ, cPlusOne, x), true) };
		}
		case ":" + ProofRules.FARKAS: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] ineqs = (Term[]) annots[0].getValue();
			assert annots.length == 2;
			assert annots[1].getKey() == ProofRules.ANNOT_COEFFS;
			final BigInteger[] coeffs = (BigInteger[]) annots[1].getValue();
			if (!ProofRules.checkFarkas(ineqs, coeffs)) {
				return reportViolatedSideCondition(axiom);
			}
			final HashSet<ProofLiteral> clause = new HashSet<>();
			for (int i = 0; i < ineqs.length; i++) {
				clause.add(new ProofLiteral(ineqs[i], false));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.MULPOS: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] ineqs = (Term[]) annots[0].getValue();
			assert annots.length == 0;
			if (!ProofRules.checkMulPos(ineqs)) {
				return reportViolatedSideCondition(axiom);
			}
			final HashSet<ProofLiteral> clause = new HashSet<>();
			for (int i = 0; i < ineqs.length; i++) {
				clause.add(new ProofLiteral(ineqs[i], i == ineqs.length - 1));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.POLYADD: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			if (!ProofRules.checkPolyAdd(params[0], params[1])) {
				return reportViolatedSideCondition(axiom);
			}
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[1]), true) };
		}
		case ":" + ProofRules.POLYMUL: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			if (!ProofRules.checkPolyMul(params[0], params[1])) {
				return reportViolatedSideCondition(axiom);
			}
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[1]), true) };
		}
		case ":" + ProofRules.TOREALDEF: {
			if (!theory.getLogic().isIRA()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 1;
			final Term lhs = theory.term(SMTLIBConstants.TO_REAL, params[0]);
			final Term rhs = ProofRules.computePolyToReal(params[0]);
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, rhs), true) };
		}
		case ":" + ProofRules.DIVIDEDEF: {
			if (!theory.getLogic().hasReals()) {
				reportError("Proof requires real arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length >= 2;
			final Term divide = theory.term(SMTLIBConstants.DIVIDE, params);
			final Term[] mulParams = new Term[params.length];
			System.arraycopy(params, 1, mulParams, 0, params.length - 1);
			mulParams[params.length - 1] = divide;
			final Term lhs = theory.term(SMTLIBConstants.MUL, mulParams);
			final LinkedHashSet<ProofLiteral> clause = new LinkedHashSet<>();
			clause.add(new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, params[0]), true));
			for (int i = 1; i < params.length; i++) {
				clause.add(new ProofLiteral(
						theory.term(SMTLIBConstants.EQUALS, params[i], Rational.ZERO.toTerm(params[i].getSort())),
						true));
			}
			return clause.toArray(new ProofLiteral[clause.size()]);
		}
		case ":" + ProofRules.MINUSDEF: {
			if (!theory.getLogic().isArithmetic()) {
				reportError("Proof requires arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length >= 1;
			final Term lhs = theory.term(SMTLIBConstants.MINUS, params);
			final Term rhs = ProofRules.computePolyMinus(lhs);
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, lhs, rhs), true) };
		}
		case ":" + ProofRules.DIVISIBLEDEF: {
			if (!theory.getLogic().hasIntegers()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			assert annots.length == 2;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			assert annots[1].getKey() == ProofRules.ANNOT_DIVISOR;
			final BigInteger divisor = (BigInteger) annots[1].getValue();
			final Term arg = params[0];
			if (divisor.signum() <= 0 || !arg.getSort().getName().equals(SMTLIBConstants.INT)) {
				return reportViolatedSideCondition(axiom);
			}
			final Term divisorTerm = Rational.valueOf(divisor, BigInteger.ONE).toTerm(arg.getSort());
			final Term divisibleTerm = theory.term(SMTLIBConstants.DIVISIBLE, new String[] { divisor.toString() }, null,
					arg);
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisorTerm);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisorTerm, divTerm);
			final Term equalTerm = theory.term(SMTLIBConstants.EQUALS, arg, mulDivTerm);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisibleTerm, equalTerm), true) };
		}
		case ":" + ProofRules.TOINTLOW: {
			if (!theory.getLogic().isIRA()) {
				reportError("Proof requires integer and real arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 1;
			final Term arg = params[0];
			final Term toRealToInt = theory.term(SMTLIBConstants.TO_REAL, theory.term(SMTLIBConstants.TO_INT, arg));
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, toRealToInt, arg), true) };
		}
		case ":" + ProofRules.TOINTHIGH: {
			if (!theory.getLogic().isIRA()) {
				reportError("Proof requires integer and real arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 1;
			final Term arg = params[0];
			final Term toRealToInt = theory.term(SMTLIBConstants.TO_REAL, theory.term(SMTLIBConstants.TO_INT, arg));
			final Term toRealPlusOne = theory.term(SMTLIBConstants.PLUS, toRealToInt,
					Rational.ONE.toTerm(arg.getSort()));
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LT, arg, toRealPlusOne), true) };
		}
		case ":" + ProofRules.DIVLOW: {
			if (!theory.getLogic().hasIntegers()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			final Term arg = params[0];
			final Term divisor = params[1];
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
			final Term zero = Rational.ZERO.toTerm(divisor.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LEQ, mulDivTerm, arg), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
		}
		case ":" + ProofRules.DIVHIGH: {
			if (!theory.getLogic().hasIntegers()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			final Term arg = params[0];
			final Term divisor = params[1];
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
			final Term mulDivTermPlus = theory.term(SMTLIBConstants.PLUS, mulDivTerm,
					theory.term(SMTLIBConstants.ABS, divisor));
			final Term zero = Rational.ZERO.toTerm(divisor.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.LT, arg, mulDivTermPlus), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
		}
		case ":" + ProofRules.MODDEF: {
			if (!theory.getLogic().hasIntegers()) {
				reportError("Proof requires integer arithmetic");
				return getTrueClause(theory);
			}
			final Term[] params = (Term[]) annots[0].getValue();
			assert annots.length == 1;
			assert params.length == 2;
			final Term arg = params[0];
			final Term divisor = params[1];
			final Term divTerm = theory.term(SMTLIBConstants.DIV, arg, divisor);
			final Term mulDivTerm = theory.term(SMTLIBConstants.MUL, divisor, divTerm);
			final Term modTerm = theory.term(SMTLIBConstants.MOD, arg, divisor);
			final Term modDef = theory.term(SMTLIBConstants.PLUS, mulDivTerm, modTerm);
			final Term zero = Rational.ZERO.toTerm(divisor.getSort());
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, modDef, arg), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, divisor, zero), true) };
		}
		case ":" + ProofRules.SELECTSTORE1: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 3;

			// (= (select (store a i v) i) v)
			final Term store = theory.term(SMTLIBConstants.STORE, params[0], params[1], params[2]);
			final Term selectStore = theory.term(SMTLIBConstants.SELECT, store, params[1]);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, selectStore, params[2]), true) };
		}
		case ":" + ProofRules.SELECTSTORE2: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 4;

			// (= (select (store a i v) j) (select a j))
			final Term store = theory.term(SMTLIBConstants.STORE, params[0], params[1], params[2]);
			final Term selectStore = theory.term(SMTLIBConstants.SELECT, store, params[3]);
			final Term select = theory.term(SMTLIBConstants.SELECT, params[0], params[3]);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, selectStore, select), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[1], params[3]), true) };
		}
		case ":" + ProofRules.EXTDIFF: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;

			// (= a b), ~(= (select a (@diff a b)) (select b (@diff a b)))
			final Term diff = theory.term(SMTInterpolConstants.DIFF, params[0], params[1]);
			final Term select0 = theory.term(SMTLIBConstants.SELECT, params[0], diff);
			final Term select1 = theory.term(SMTLIBConstants.SELECT, params[1], diff);
			return new ProofLiteral[] {
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, params[0], params[1]), true),
					new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, select0, select1), false) };
		}
		case ":" + ProofRules.CONST: {
			if (!theory.getLogic().isArray()) {
				reportError("Proof requires array theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 2;
			final Term value = params[0];
			final Term index = params[1];

			// (= (select (const value) index) value)
			final Sort arraySort = theory.getSort(SMTLIBConstants.ARRAY, index.getSort(), value.getSort());
			final Term constArray = theory.term(SMTLIBConstants.CONST, null, arraySort, value);
			final Term select = theory.term(SMTLIBConstants.SELECT, constArray, index);
			return new ProofLiteral[] { new ProofLiteral(theory.term(SMTLIBConstants.EQUALS, select, value), true) };
		}
		case ":" + ProofRules.DT_PROJECT: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final ApplicationTerm selConsTerm = (ApplicationTerm) params[0];
			final FunctionSymbol selector = selConsTerm.getFunction();
			assert selector.isSelector();
			final ApplicationTerm consTerm = (ApplicationTerm) selConsTerm.getParameters()[0];
			if (!consTerm.getFunction().isConstructor()) {
				return reportViolatedSideCondition(axiom);
			}
			final DataType dataType = (DataType) consTerm.getSort().getSortSymbol();
			final Constructor cons = dataType.getConstructor(consTerm.getFunction().getName());
			final int selectPos = cons.getSelectorIndex(selector.getName());
			final Term consArg = consTerm.getParameters()[selectPos];

			// + (= (seli (cons a1 ... an)) ai)
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, selConsTerm, consArg);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.DT_CONS: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final ApplicationTerm isConsTerm = (ApplicationTerm) params[0];
			if (!isConsTerm.getFunction().getName().equals(SMTLIBConstants.IS)) {
				return reportViolatedSideCondition(axiom);
			}
			final Term dataTerm = isConsTerm.getParameters()[0];
			final DataType dataType = (DataType) dataTerm.getSort().getSortSymbol();
			final Constructor cons = dataType.getConstructor(isConsTerm.getFunction().getIndices()[0]);
			final String[] selectors = cons.getSelectors();
			final Term[] selectTerms = new Term[selectors.length];
			for (int i = 0; i < selectors.length; i++) {
				selectTerms[i] = theory.term(selectors[i], dataTerm);
			}
			final Term consTerm = theory.term(cons.getName(), null,
					(cons.needsReturnOverload() ? dataTerm.getSort() : null), selectTerms);

			// - ((_ is cons) u), + (= (cons (sel1 u) ... (seln u)) u)
			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, consTerm, dataTerm);
			return new ProofLiteral[] { new ProofLiteral(isConsTerm, false), new ProofLiteral(provedEq, true) };
		}
		case ":" + ProofRules.DT_TESTI: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final ApplicationTerm consTerm = (ApplicationTerm) params[0];
			final FunctionSymbol consFunc = consTerm.getFunction();
			if (!consFunc.isConstructor()) {
				return reportViolatedSideCondition(axiom);
			}
			final Term isTerm = theory.term(SMTLIBConstants.IS, new String[] { consFunc.getName() }, null, consTerm);

			// + ((_ is cons) (cons a1 ... an))
			return new ProofLiteral[] { new ProofLiteral(isTerm, true) };
		}
		case ":" + ProofRules.DT_TESTE: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 2;
			final String otherCons = (String) params[0];
			final ApplicationTerm consTerm = (ApplicationTerm) params[1];
			final FunctionSymbol consFunc = consTerm.getFunction();
			if (!consFunc.isConstructor() || consFunc.getName().equals(otherCons)) {
				return reportViolatedSideCondition(axiom);
			}
			final Term isTerm = theory.term(SMTLIBConstants.IS, new String[] { otherCons }, null, consTerm);

			// + ((_ is otherCons) (cons a1 ... an))
			return new ProofLiteral[] { new ProofLiteral(isTerm, false) };
		}
		case ":" + ProofRules.DT_EXHAUST: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			final Term data = params[0];
			final DataType dataType = (DataType) data.getSort().getSortSymbol();
			final Constructor[] constrs = dataType.getConstructors();
			// + ((_ is cons0) data) ... + ((_ is consn) data)
			final ProofLiteral[] lits = new ProofLiteral[constrs.length];
			for (int i = 0; i < lits.length; i++) {
				final Term tester = theory.term(SMTLIBConstants.IS, new String[] { constrs[i].getName() }, null, data);
				lits[i] = new ProofLiteral(tester, true);
			}
			return lits;
		}
		case ":" + ProofRules.DT_ACYCLIC: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Object[] params = (Object[]) annots[0].getValue();
			assert params.length == 2;
			final Term consTerm = (Term) params[0];
			final int[] positions = (int[]) params[1];
			if (positions.length == 0) {
				return reportViolatedSideCondition(axiom);
			}
			Term subTerm = consTerm;
			for (final int pos : positions) {
				final ApplicationTerm parent = (ApplicationTerm) subTerm;
				if (!parent.getFunction().isConstructor()) {
					return reportViolatedSideCondition(axiom);
				}
				subTerm = parent.getParameters()[pos];
			}
			final Term provedIneq = theory.term(SMTLIBConstants.EQUALS, consTerm, subTerm);
			return new ProofLiteral[] { new ProofLiteral(provedIneq, false) };
		}
		case ":" + ProofRules.DT_MATCH: {
			if (!theory.getLogic().isDatatype()) {
				reportError("Proof requires data type theory");
				return getTrueClause(theory);
			}
			assert annots.length == 1;
			final Term[] params = (Term[]) annots[0].getValue();
			assert params.length == 1;
			if (!(params[0] instanceof MatchTerm)) {
				return reportViolatedSideCondition(axiom);
			}
			final MatchTerm matchTerm = (MatchTerm) params[0];
			final Term iteTerm = buildIteForMatch(matchTerm);

			final Term provedEq = theory.term(SMTLIBConstants.EQUALS, matchTerm, iteTerm);
			return new ProofLiteral[] { new ProofLiteral(provedEq, true) };
		}
		default:
			reportError("Unknown axiom %s", axiom);
			return getTrueClause(axiom.getTheory());
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

	private static Term buildLetForMatch(final Constructor constr, final TermVariable[] vars, final Term dataTerm,
			final Term caseTerm) {
		final Theory theory = dataTerm.getTheory();
		final Term[] selectTerms = new Term[vars.length];
		if (constr == null) {
			assert vars.length == 1;
			selectTerms[0] = dataTerm;
		} else {
			assert constr.getSelectors().length == vars.length;
			for (int i = 0; i < vars.length; i++) {
				selectTerms[i] = theory.term(constr.getSelectors()[i], dataTerm);
			}
		}
		return new FormulaUnLet().unlet(theory.let(vars, selectTerms, caseTerm));
	}

	public static Term buildIteForMatch(final MatchTerm matchTerm) {
		final Theory theory = matchTerm.getTheory();
		final Term dataTerm = matchTerm.getDataTerm();
		final Term[] cases = matchTerm.getCases();
		final TermVariable[][] vars = matchTerm.getVariables();
		final Constructor[] constrs = matchTerm.getConstructors();

		Term iteTerm;
		iteTerm = buildLetForMatch(constrs[constrs.length - 1], vars[constrs.length - 1], dataTerm,
				cases[constrs.length - 1]);
		for (int i = constrs.length - 2; i >= 0; i--) {
			final Term caseTerm = buildLetForMatch(constrs[i], vars[i], dataTerm, cases[i]);
			if (constrs[i] == null) {
				// SMT-LIB standard allows the default case in the middle, with the semantics
				// that
				// all following cases are redundant.
				iteTerm = caseTerm;
			} else {
				final Term condTerm = theory.term(SMTLIBConstants.IS, new String[] { constrs[i].getName() }, null,
						dataTerm);
				iteTerm = theory.term(SMTLIBConstants.ITE, condTerm, caseTerm, iteTerm);
			}
		}
		return iteTerm;
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
			final LambdaTerm def = (LambdaTerm) annotValues[1];
			if (!func.isIntern() && func.getDefinition() != null
					&& (func.getDefinition() != def.getSubterm()
							|| !Arrays.equals(func.getDefinitionVars(), def.getVariables()))) {
				throw new AssertionError("Inconsistent function definition.");
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
}
