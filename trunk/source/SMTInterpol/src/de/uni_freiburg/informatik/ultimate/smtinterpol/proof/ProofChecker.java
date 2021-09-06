/*
 * Copyright (C) 2009-2017 University of Freiburg
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
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * This proof checker checks compliance of SMTInterpol proofs with its documented format.
 *
 * @author Pascal Raiola, Jochen Hoenicke, Tanja Schindler
 */
public class ProofChecker extends NonRecursive {

	/*
	 * The proof checker uses a non-recursive iteration through the proof tree. The main type in a proof tree is the
	 * sort {@literal @}Proof. Each term of this sort proves a formula and the main task of this code is to compute the
	 * proven formula. The whole proof term should prove the formula false.
	 *
	 * The main idea of this non-recursive algorithm is to push a proof walker for the {@literal @}Proof terms on the
	 * todo stack, which will push the proved term of type Bool onto the result stack mStackResults. To handle functions
	 * like {@literal @}eq, {@literal @}cong, {@literal @}trans that take a {@literal @}Proof term as input, first a
	 * XYWalker the function XY is pushed on the todo stack and then the ProofWalker for the {@literal @}Proof terms are
	 * pushed. The Walker will then call the corresponding walkXY function which checks the proved arguments, computes
	 * the final proved formula and pushes that on the result stack.
	 *
	 * Simple functions that don't take {@literal @}Proof arguments are handled directly by calling the walkXY function.
	 */

	/**
	 * The main proof walker that handles a term of sort {@literal @}Proof. It just calls the walk function.
	 */
	static class ProofWalker implements Walker {
		final ApplicationTerm mTerm;

		public ProofWalker(final Term term) {
			assert term.getSort().getName().equals(ProofConstants.SORT_PROOF);
			mTerm = (ApplicationTerm) term;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((ProofChecker) engine).walk(mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}res application term after its arguments are converted. It just calls
	 * the walkResolution function.
	 */
	static class ResolutionWalker implements Walker {
		final ApplicationTerm mTerm;

		public ResolutionWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_RES);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			engine.enqueueWalker(this);
			final Term[] params = mTerm.getParameters();
			for (int i = params.length - 1; i >= 1; i--) {
				final AnnotatedTerm pivotClause = (AnnotatedTerm) params[i];
				engine.enqueueWalker(new ProofWalker(pivotClause.getSubterm()));
			}
			engine.enqueueWalker(new ProofWalker(params[0]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term[] subProofs = new Term[mTerm.getParameters().length];
			for (int i = subProofs.length - 1; i >= 1; i--) {
				subProofs[i] = checker.stackPop();
			}
			subProofs[0] = checker.stackPop();
			checker.stackPush(checker.walkResolution(mTerm, subProofs), mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}mp application term after its arguments are converted. It just calls
	 * the walkEquality function.
	 */
	static class ModusPonensWalker implements Walker {
		final ApplicationTerm mTerm;

		public ModusPonensWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_MP);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			assert params.length == 2;
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(params[1]));
			engine.enqueueWalker(new ProofWalker(params[0]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term rewrite = checker.stackPop();
			final Term origFormula = checker.stackPop();
			checker.stackPush(checker.walkModusPonens(mTerm, origFormula, rewrite), mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}clause application after its first argument is converted. It just
	 * calls the walkClause function.
	 */
	static class ClauseWalker implements Walker {
		final ApplicationTerm mTerm;

		public ClauseWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_CLAUSE);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(mTerm.getParameters()[0]));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term subProof = checker.stackPop();
			checker.stackPush(checker.walkClause(mTerm, subProof), mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}split application after its first argument is converted. It just
	 * calls the walkSplit function.
	 */
	static class SplitWalker implements Walker {
		final ApplicationTerm mTerm;

		public SplitWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_SPLIT);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term subproof = mTerm.getParameters()[0];
			/* split expects an annotated proof as first parameter */
			if (!(subproof instanceof AnnotatedTerm)) {
				// push dummy proof as result an return
				engine.reportError("Split without annotation: " + mTerm);
				engine.stackPush(null, mTerm);
				return;
			}
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(((AnnotatedTerm) subproof).getSubterm()));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			checker.stackPush(checker.walkSplit(mTerm, checker.stackPop()), mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}cong application after its arguments are converted. It just calls the
	 * walkCongruence function.
	 */
	static class CongruenceWalker implements Walker {
		final ApplicationTerm mTerm;

		public CongruenceWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_CONG);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			for (int i = params.length - 1; i >= 0; i--) {
				engine.enqueueWalker(new ProofWalker(params[i]));
			}

		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term[] params = mTerm.getParameters();
			final Term[] subProofs = new Term[params.length];
			for (int i = params.length - 1; i >= 0; i--) {
				subProofs[i] = checker.stackPop();
			}
			checker.stackPush(checker.walkCongruence(mTerm, subProofs), mTerm);
		}
	}

	static class OrMonotonyWalker implements Walker {
		final ApplicationTerm mTerm;

		public OrMonotonyWalker(final ApplicationTerm term) {
			assert term.getFunction().getName() == ProofConstants.FN_ORMONOTONY;
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			for (int i = params.length - 1; i >= 0; i--) {
				engine.enqueueWalker(new ProofWalker(params[i]));
			}
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term[] params = mTerm.getParameters();
			final Term[] subProofs = new Term[params.length];
			for (int i = params.length - 1; i >= 0; i--) {
				subProofs[i] = checker.stackPop();
			}
			checker.stackPush(checker.walkOrMonotony(mTerm, subProofs), mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}exists application after its arguments are converted. It just calls
	 * the walkExists function.
	 */
	static class ExistsWalker implements Walker {
		final ApplicationTerm mTerm;

		public ExistsWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_EXISTS);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			assert params.length == 1;
			assert params[0] instanceof AnnotatedTerm;
			engine.enqueueWalker(new ProofWalker(((AnnotatedTerm) params[0]).getSubterm()));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term subProof = checker.stackPop();
			checker.stackPush(checker.walkExists(mTerm, subProof), mTerm);
		}
	}

	static class AllIntroWalker implements Walker {
		final ApplicationTerm mTerm;

		public AllIntroWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_ALLINTRO);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			assert params.length == 1;
			assert params[0] instanceof AnnotatedTerm;
			engine.enqueueWalker(this);
			engine.enqueueWalker(new ProofWalker(((AnnotatedTerm) params[0]).getSubterm()));
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			checker.stackPush(checker.walkAllIntro(mTerm, checker.stackPop()), mTerm);
		}
	}

	/**
	 * The proof walker that handles a {@literal @}trans application after its arguments are converted. It just calls
	 * the walkTransitivity function.
	 */
	static class TransitivityWalker implements Walker {
		final ApplicationTerm mTerm;

		public TransitivityWalker(final ApplicationTerm term) {
			assert term.getFunction().getName().equals(ProofConstants.FN_TRANS);
			mTerm = term;
		}

		public void enqueue(final ProofChecker engine) {
			final Term[] params = mTerm.getParameters();
			engine.enqueueWalker(this);
			for (int i = params.length - 1; i >= 0; i--) {
				engine.enqueueWalker(new ProofWalker(params[i]));
			}
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;
			final Term[] params = mTerm.getParameters();
			final Term[] subProofs = new Term[params.length];
			for (int i = params.length - 1; i >= 0; i--) {
				subProofs[i] = checker.stackPop();
			}
			checker.stackPush(checker.walkTransitivity(mTerm, subProofs), mTerm);
		}
	}

	/**
	 * The proof walker that handles an {@literal @}inst application after the subproof has been checked.
	 */
	static class InstLemmaWalker implements Walker {
		private final Term[] mClause;
		private final Term[] mSubstitution;

		InstLemmaWalker(final Term[] clause, final Term[] substitution) {
			mClause = clause;
			mSubstitution = substitution;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final ProofChecker checker = (ProofChecker) engine;

			assert checker.isApplication("not", mClause[0]);
			final Term firstAtom = checker.unquote(((ApplicationTerm) mClause[0]).getParameters()[0]);
			assert firstAtom instanceof QuantifiedFormula && ((QuantifiedFormula) firstAtom).getQuantifier() == 1;
			final QuantifiedFormula forallLit = (QuantifiedFormula) firstAtom;
			final TermVariable[] vars = forallLit.getVariables();
			assert forallLit.getQuantifier() == 1;

			if (vars.length != mSubstitution.length) {
				checker.reportError("Lemma :inst needs substitution for all quantified variables.");
				return;
			}
			final Map<TermVariable, Term> sigma = new HashMap<>();
			for (int i = 0; i < vars.length; i++) {
				sigma.put(vars[i], mSubstitution[i]);
			}
			final Term[] substClause = checker.substituteInQuantClause(forallLit.getSubformula(), sigma);

			// Check that an equality has been proven where the first parameter must match the substituted clause, and
			// the second parameter must contain exactly the inst clause literals (but may have a different order).
			final Term proved = checker.stackPop();
			if (!(proved instanceof ApplicationTerm)
					|| ((ApplicationTerm) proved).getFunction().getName() != "=") {
				checker.reportError("Lemma :inst needs subproof for term equality.");
				return;
			}
			final ApplicationTerm provedEq = (ApplicationTerm) proved;
			final Set<Term> proofInputLits =
					new HashSet<>(Arrays.asList(checker.termToClause(provedEq.getParameters()[0])));
			final Set<Term> proofOutputLits =
					new HashSet<>(Arrays.asList(checker.termToClause(provedEq.getParameters()[1])));
			final Set<Term> substLits = new HashSet<>(Arrays.asList(substClause));
			final Set<Term> instLits = new HashSet<>(Arrays.asList(Arrays.copyOfRange(mClause, 1, mClause.length)));
			if (!proofInputLits.equals(substLits) || !proofOutputLits.equals(instLits)) {
				checker.reportError("Previously proved term equality does not match literals in lemma :inst.");
				return;
			}

		}
	}

	/**
	 * The set of all asserted terms (collected from the script by calling getAssertions()). This is used to check the
	 * {@literal @}asserted rules.
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
	 * The number of reported errors.
	 */
	int mError;

	/**
	 * The proof cache. It maps each converted proof to the boolean term it proves.
	 */
	HashMap<Term, Term> mCacheConv;

	/**
	 * The result stack. This contains the terms proved by the proof terms.
	 */
	Stack<Term> mStackResults = new Stack<>();

	/**
	 * Defined quantified terms. This contains the {@literal @}AUX terms. TODO and the skolem terms.
	 */
	HashMap<ApplicationTerm, Term> mQuantDefinedTerms;

	/**
	 * Skolem terms. This contains for each skolem function the existentially
	 * quantified formula and the variable for which it was created.
	 */
	HashMap<FunctionSymbol, Pair<Term, TermVariable>> mSkolemFunctions;

	/**
	 * Statistics.
	 */
	private int mNumInstancesUsed;
	private int mNumInstancesFromDER;
	private int mNumInstancesFromConflictUnitSearch;
	private int mNumInstancesFromEMatching;
	private int mNumInstancesFromEnumeration;

	/**
	 * Create a proof checker.
	 *
	 * @param script
	 *            An SMT2 script.
	 * @param logger
	 *            The logger where errors are reported.
	 */
	public ProofChecker(final Script script, final LogProxy logger) {
		mSkript = script;
		mLogger = logger;
	}

	/**
	 * Check a proof for consistency. This reports errors on the logger.
	 *
	 * @param proof
	 *            the proof to check.
	 * @return true, if no errors were found.
	 */
	public boolean check(Term proof) {
		final FormulaUnLet unletter = new FormulaUnLet();
		final Term[] assertions = mSkript.getAssertions();
		mAssertions = new HashSet<>(assertions.length);
		for (final Term ass : assertions) {
			mAssertions.add(unletter.transform(ass));
		}

		// Initializing the proof-checker-cache
		mCacheConv = new HashMap<>();
		mQuantDefinedTerms = new HashMap<>();
		mSkolemFunctions = new HashMap<>();
		mError = 0;
		// Now non-recursive:
		proof = unletter.unlet(proof);
		run(new ProofWalker(proof));

		assert (mStackResults.size() == 1);
		final Term result = stackPop();
		if (result != null && !isApplication("false", result)) {
			reportError("The proof did not yield a contradiction but " + result);
		}
		// clear state
		mAssertions = null;
		mCacheConv = null;

		// TODO Handle this in a better way (e.g. as part of statistics)
		if (proof.getTheory().getLogic().isQuantified()) {
			mLogger.warn(
					"Proof: Instances of quantified clauses used: %d (DER: %d Conflict/unit search: %d E-matching: %d Enumeration: %d)",
					mNumInstancesUsed, mNumInstancesFromDER, mNumInstancesFromConflictUnitSearch,
					mNumInstancesFromEMatching, mNumInstancesFromEnumeration);
		}
		return mError == 0;
	}

	private void reportError(final String msg) {
		mLogger.error(msg);
		mError++;
	}

	private void reportWarning(final String msg) {
		mLogger.warn(msg);
	}

	/**
	 * The proof walker. This takes a proof term and pushes the proven formula on the result stack. It also checks the
	 * proof cache to prevent running over the same term twice.
	 *
	 * @param proofTerm
	 *            The proof term. Its sort must be {@literal @}Proof.
	 */
	void walk(final ApplicationTerm proofTerm) {
		/* Check the cache, if the unfolding step was already done */
		if (mCacheConv.containsKey(proofTerm)) {
			stackPush(mCacheConv.get(proofTerm), proofTerm);
			return;
		}

		/* Get the function and parameters */
		final String rulename = proofTerm.getFunction().getName();

		/* Look at the rule name and treat each different */
		switch (rulename) {
		case ProofConstants.FN_RES:
			/*
			 * The resolution rule.
			 *
			 * This function is expected to have as first argument the main clause. The other parameters are clauses
			 * annotated with a pivot literal, on which they are resolved.
			 */
			new ResolutionWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_MP:
			new ModusPonensWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_CONG:
			new CongruenceWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_ORMONOTONY:
			new OrMonotonyWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_TRANS:
			new TransitivityWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_REFL:
			stackPush(walkReflexivity(proofTerm), proofTerm);
			break;

		case ProofConstants.FN_LEMMA:
			stackPush(walkLemma(proofTerm), proofTerm);
			break;

		case ProofConstants.FN_TAUTOLOGY:
			stackPush(walkTautology(proofTerm), proofTerm);
			break;

		case ProofConstants.FN_ASSERTED:
			stackPush(walkAsserted(proofTerm), proofTerm);
			break;

		case ProofConstants.FN_REWRITE:
			stackPush(walkRewrite(proofTerm), proofTerm);
			break;

		case ProofConstants.FN_SPLIT:
			new SplitWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_CLAUSE:
			new ClauseWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_EXISTS:
			new ExistsWalker(proofTerm).enqueue(this);
			break;

		case ProofConstants.FN_ALLINTRO:
			new AllIntroWalker(proofTerm).enqueue(this);
			break;

		default:
			reportError("Unknown proof rule " + rulename + ".");
			stackPush(null, proofTerm);
			break;
		}
	}

	/* === Theory lemmas === */

	/**
	 * Walk a lemma rule. This checks the correctness of the lemma and returns the lemma, which is always the annotated
	 * sub term of this application. The result is pushed to the stack instead of being returned.
	 *
	 * If the lemma cannot be verified, an error is reported but the lemma is still used to check the remainder of the
	 * proof.
	 *
	 * @param lemmaApp
	 *            The {@literal @}lemma application.
	 */
	Term walkLemma(final ApplicationTerm lemmaApp) {
		/*
		 * The argument of the @lemma application is a single clause annotated with the lemma type, which has as object
		 * all the necessary annotation. For example (@lemma (! (or (not (= a b)) (not (= b c)) (= a c)) :CC ((= a c)
		 * :path (a b c))))
		 */
		if (!(lemmaApp.getParameters()[0] instanceof AnnotatedTerm)) {
			reportError("Malformed lemma " + lemmaApp);
			return null;
		}
		final AnnotatedTerm annTerm = (AnnotatedTerm) lemmaApp.getParameters()[0];
		final String lemmaType = annTerm.getAnnotations()[0].getKey();
		final Object lemmaAnnotation = annTerm.getAnnotations()[0].getValue();
		final Term lemma = annTerm.getSubterm();
		final Term[] clause = termToClause(lemma);

		if (lemmaType == ":LA") {
			checkLALemma(clause, (Term[]) lemmaAnnotation);
		} else if (lemmaType == ":CC") {
			checkCCLemma(clause, (Object[]) lemmaAnnotation);
		} else if (lemmaType == ":CC" || lemmaType == ":read-over-weakeq" || lemmaType == ":weakeq-ext"
				|| lemmaType == ":read-const-weakeq" || lemmaType == ":const-weakeq") {
			checkArrayLemma(lemmaType, clause, (Object[]) lemmaAnnotation);
		} else if (lemmaType == ":dt-project" || lemmaType == ":dt-tester" || lemmaType == ":dt-constructor"
				|| lemmaType == ":dt-cases" || lemmaType == ":dt-unique" || lemmaType == ":dt-injective"
				|| lemmaType == ":dt-disjoint" || lemmaType == ":dt-cycle") {
			reportWarning("Unchecked datatype lemma " + annTerm);
			checkDataTypeLemma(lemmaType, clause, (Object[]) lemmaAnnotation);
		} else if (lemmaType == ":trichotomy") {
			checkTrichotomy(clause);
		} else if (lemmaType == ":EQ") {
			checkEQLemma(clause);
		} else if (lemmaType == ":inst") {
			mNumInstancesUsed++;
			final Object[] subannots = ((Object[]) lemmaAnnotation);
			assert subannots.length == 5;
			final String solverPart = (String) subannots[2];
			if (solverPart == ":conflict") {
				mNumInstancesFromConflictUnitSearch++;
			} else if (solverPart == ":e-matching") {
				mNumInstancesFromEMatching++;
			} else {
				assert solverPart == ":enumeration";
				mNumInstancesFromEnumeration++;
			}
			checkInstLemma(clause, subannots);
		} else {
			reportError("Cannot deal with lemma " + lemmaType);
			mLogger.error(annTerm);
		}

		return lemma;
	}

	/**
	 * Check a CC lemma for correctness. If a problem is found, an error is reported.
	 *
	 * @param clause
	 *            the clause to check
	 * @param ccAnnotation
	 *            the argument of the :CC annotation.
	 */
	private void checkCCLemma(final Term[] clause, final Object[] ccAnnotation) {
		if (ccAnnotation.length < 3 || !(ccAnnotation[0] instanceof Term) || ccAnnotation[1] != ":subpath"
				|| !(ccAnnotation[2] instanceof Term[])) {
			reportError("Malformed CC annotation");
			return;
		}
		final int startSubpathAnnot = 1;

		// The goal equality
		final Term goalEquality = unquote((Term) ccAnnotation[0]);

		/* collect literals and search for the disequality */
		final HashSet<SymmetricPair<Term>> allEqualities = new HashSet<>();
		boolean foundDiseq = false;
		for (final Term literal : clause) {
			if (isApplication("not", literal)) {
				Term atom = ((ApplicationTerm) literal).getParameters()[0];
				atom = unquote(atom);
				if (!isApplication("=", atom)) {
					reportError("Unknown literal in CC lemma.");
					return;
				}
				final Term[] sides = ((ApplicationTerm) atom).getParameters();
				if (sides.length != 2) {
					reportError("Expected binary equality, found " + atom);
					return;
				}
				allEqualities.add(new SymmetricPair<>(sides[0], sides[1]));
			} else {
				if (unquote(literal) != goalEquality || foundDiseq) {
					reportError("Unexpected positive literal in CC lemma.");
				}
				foundDiseq = true;
			}
		}

		final Term[] mainPath = (Term[]) ccAnnotation[startSubpathAnnot + 1];
		if (mainPath.length < 2) {
			reportError("Main path too short in CC lemma");
			return;
		}
		if (!isApplication("=", goalEquality)) {
			reportError("Goal equality is not an equality in CC lemma");
			return;
		}
		final Term[] sides = ((ApplicationTerm) goalEquality).getParameters();
		if (sides.length != 2) {
			reportError("Expected binary equality in CC lemma");
			return;
		}
		if (!foundDiseq && !checkTrivialDisequality(sides[0], sides[1])) {
			reportError("Did not find goal equality in CC lemma");
		}
		if (!new SymmetricPair<>(mainPath[0], mainPath[mainPath.length - 1])
				.equals(new SymmetricPair<>(sides[0], sides[1]))) {
			reportError("Did not explain main equality " + goalEquality);
		}

		if (mainPath.length == 2) {
			// This must be a congruence lemma
			if (!(mainPath[0] instanceof ApplicationTerm) || !(mainPath[1] instanceof ApplicationTerm)) {
				reportError("Malformed congruence lemma");
				return;
			}
			final ApplicationTerm lhs = (ApplicationTerm) mainPath[0];
			final ApplicationTerm rhs = (ApplicationTerm) mainPath[1];
			// check if functions are the same and have the same number of parameters
			if (lhs.getFunction() != rhs.getFunction() || lhs.getParameters().length != rhs.getParameters().length) {
				reportError("Malformed congruence lemma");
				return;
			}
			// check if each parameter is identical or equal
			final Term[] lhsArgs = lhs.getParameters();
			final Term[] rhsArgs = rhs.getParameters();
			for (int i = 0; i < lhsArgs.length; i++) {
				if (lhsArgs[i] != rhsArgs[i] && !allEqualities.contains(new SymmetricPair<>(lhsArgs[i], rhsArgs[i]))) {
					reportError("Malformed congruence lemma");
				}
			}
		} else {
			// This is a transitivity lemma
			for (int i = 0; i < mainPath.length - 1; i++) {
				if (!allEqualities.contains(new SymmetricPair<>(mainPath[i], mainPath[i + 1]))) {
					reportError("Equality missing in transitivity lemma");
				}
			}
		}
	}

	/**
	 * Check an array lemma for correctness. If a problem is found, an error is reported.
	 *
	 * @param type
	 *            the lemma type
	 * @param clause
	 *            the clause to check
	 * @param ccAnnotation
	 *            the argument of the :CC annotation.
	 */
	private void checkArrayLemma(final String type, final Term[] clause, final Object[] ccAnnotation) {
		if (ccAnnotation.length < 3) {
			reportError("Malformed Array annotation");
			return;
		}
		final boolean isWeakEqExt = type == ":weakeq-ext";
		final boolean noIndexOnMain = isWeakEqExt || type == ":const-weakeq";
		/*
		 * weakPaths maps from a symmetric pair to the set of weak indices such that a weak path was proven for this
		 * pair. strongPaths contains the sets of all proven strong paths.
		 */
		final HashSet<SymmetricPair<Term>> allEqualities = new HashSet<>();
		/* indexDiseqs contains all index equalities in the clause */
		final HashSet<SymmetricPair<Term>> allDisequalities = new HashSet<>();

		/* collect literals and search for the disequality */
		for (final Term literal : clause) {
			final boolean negated = isApplication("not", literal);
			final Term atom = unquote(negated ? ((ApplicationTerm) literal).getParameters()[0] : literal);
			if (!isApplication("=", atom)) {
				reportError("Unknown literal in array lemma.");
				return;
			}
			final Term[] sides = ((ApplicationTerm) atom).getParameters();
			if (sides.length != 2) {
				reportError("Unknown literal in array lemma.");
				return;
			}
			if (negated) {
				// negated atom in clause -> equality in conflict
				allEqualities.add(new SymmetricPair<>(sides[0], sides[1]));
			} else {
				allDisequalities.add(new SymmetricPair<>(sides[0], sides[1]));
			}
		}
		final Term goalEquality = unquote((Term) ccAnnotation[0]);
		if (!isApplication("=", goalEquality)) {
			reportError("Goal equality is not an equality in array lemma");
			return;
		}
		final Term[] goalTerms = ((ApplicationTerm) goalEquality).getParameters();
		if (goalTerms.length != 2) {
			reportError("Expected binary equality in array lemma");
			return;
		}
		if (!allDisequalities.contains(new SymmetricPair<>(goalTerms[0], goalTerms[1]))
				&& !checkTrivialDisequality(goalTerms[0], goalTerms[1])) {
			reportError("Did not find goal equality in array lemma");
		}

		/*
		 * Check the paths in reverse order. Collect proven paths in a hash set, so that they can be used later.
		 */
		if (isWeakEqExt ? ccAnnotation.length % 2 != 1 : ccAnnotation.length != 3) {
			reportError("Malformed Array subpath");
			return;
		}
		if (ccAnnotation[1] != (noIndexOnMain ? ":subpath" : ":weakpath") || !(ccAnnotation[2] instanceof Object[])) {
			reportError("Malformed Array subpath");
			return;
		}
		Term[] mainPath;
		Term mainIdx;
		if (!noIndexOnMain) {
			final Object[] weakItems = (Object[]) ccAnnotation[2];
			if (weakItems.length != 2 || !(weakItems[0] instanceof Term) || !(weakItems[1] instanceof Term[])) {
				reportError("Malformed Array subpath");
				return;
			}
			mainIdx = (Term) weakItems[0];
			mainPath = (Term[]) weakItems[1];
		} else {
			if (!(ccAnnotation[2] instanceof Term[])) {
				reportError("Malformed Array subpath");
				return;
			}
			mainIdx = null;
			mainPath = (Term[]) ccAnnotation[2];
		}
		final SymmetricPair<Term> endPoints = new SymmetricPair<>(mainPath[0], mainPath[mainPath.length - 1]);
		/*
		 * Collect the weakpaths of weakeq ext first.
		 */
		if (isWeakEqExt) {
			final HashSet<Term> weakIndices = new HashSet<>();
			for (int i = 3; i < ccAnnotation.length; i += 2) {
				if (ccAnnotation[i] != ":weakpath" || !(ccAnnotation[i + 1] instanceof Object[])) {
					reportError("Malformed Array subpath");
					return;
				}
				final Object[] weakItems = (Object[]) ccAnnotation[i + 1];
				if (weakItems.length != 2 || !(weakItems[0] instanceof Term) || !(weakItems[1] instanceof Term[])) {
					reportError("Malformed Array subpath");
					return;
				}
				/* check weak path */
				final Term idx = (Term) weakItems[0];
				final Term[] weakPath = (Term[]) weakItems[1];
				checkArrayPath(type, idx, weakPath, allEqualities, allDisequalities, null);
				/* check end points */
				if (!endPoints.equals(new SymmetricPair<>(weakPath[0], weakPath[weakPath.length - 1]))) {
					reportError("Malformed Array weakpath");
					return;
				}
				/* remember index */
				weakIndices.add(idx);
			}

			checkArrayPath(type, null, mainPath, allEqualities, allDisequalities, weakIndices);
			// check that we proved the right equality
			if (!endPoints.equals(new SymmetricPair<>(goalTerms[0], goalTerms[1]))) {
				reportError("Wrong goal equality");
			}
		} else {
			checkArrayPath(type, mainIdx, mainPath, allEqualities, allDisequalities, null);
			switch (type) {
			case ":read-over-weakeq": {
				if (!isApplication("=", goalEquality)) {
					reportError("Wrong goal equality in read-over-weakeq lemma");
					return;
				}
				if (!isApplication("select", goalTerms[0]) || !isApplication("select", goalTerms[1])) {
					reportError("Wrong goal equality in read-over-weakeq lemma");
					return;
				}
				final Term[] p1 = ((ApplicationTerm) goalTerms[0]).getParameters();
				final Term[] p2 = ((ApplicationTerm) goalTerms[1]).getParameters();
				if (p1[1] != p2[1] && !allEqualities.contains(new SymmetricPair<>(p1[1], p2[1]))) {
					reportError("Missing index equality in read-over-weakeq lemma");
				}
				if (mainIdx != p1[1] && mainIdx != p2[1]) {
					reportError("Wrong index in weak path");
				}
				if (!endPoints.equals(new SymmetricPair<>(p1[0], p2[0]))) {
					reportError("Wrong path ends in weak path");
				}
				break;
			}
			case ":read-const-weakeq": {
				if (!isApplication("const", endPoints.getSecond())) {
					reportError("Main weak path in read-const-weakeq not to a const array.");
					return;
				}
				final Term c1 = mSkript.term("select", endPoints.getFirst(), mainIdx);
				final Term c2 = ((ApplicationTerm) endPoints.getSecond()).getParameters()[0];
				// check if goalTerms are a permutation of c1,c2
				if ((goalTerms[0] != c1 || goalTerms[1] != c2) && (goalTerms[1] != c1 || goalTerms[0] != c2)) {
					reportError("Wong goal equality in read-const-weakeq");
				}
				break;
			}
			case ":const-weakeq": {
				assert mainIdx == null;
				if (!isApplication("const", endPoints.getFirst()) || !isApplication("const", endPoints.getSecond())) {
					reportError("Main weak path in read-const-weakeq not to a const array.");
					return;
				}
				final Term v1 = ((ApplicationTerm) endPoints.getFirst()).getParameters()[0];
				final Term v2 = ((ApplicationTerm) endPoints.getSecond()).getParameters()[0];
				// check if goalTerms are a permutation of c1,c2
				if ((goalTerms[0] != v1 || goalTerms[1] != v2) && (goalTerms[1] != v1 || goalTerms[0] != v2)) {
					reportError("Wrong goal equality in const-weakeq lemma");
				}
				break;
			}
			default:
				reportError("Unknown rule " + type);
				return;
			}
		}
	}

	/**
	 * Check if each step in an array path is valid. This means, for each pair of consecutive terms, either there is a
	 * strong path between the two, or there exists a select path explaining element equality of array terms at the weak
	 * path index, or it is a weak store step, or a congruence. This reports errors using reportError.
	 *
	 * @param lemmaType
	 *            the type of array lemma.
	 * @param weakIdx
	 *            the weak path index or null for subpaths.
	 * @param path
	 *            the path to check.
	 * @param equalities
	 *            the equality literals from the clause.
	 * @param disequalities
	 *            the index disequality literals from the clause.
	 * @param weakPaths
	 *            the weak paths (given by their weak index) needed for the main path in array lemmas, null if path is
	 *            not the main path.
	 */
	void checkArrayPath(final String lemmaType, final Term weakIdx, final Term[] path,
			final HashSet<SymmetricPair<Term>> equalities, final HashSet<SymmetricPair<Term>> disequalities,
			final HashSet<Term> weakPaths) {
		// note that a read-const-weakeq path can have length 1
		if (path.length < 1) {
			reportError("Empty path in array lemma");
			return;
		}
		for (int i = 0; i < path.length - 1; i++) {
			final SymmetricPair<Term> pair = new SymmetricPair<>(path[i], path[i + 1]);
			/* check for strong path first */
			if (equalities.contains(pair)) {
				continue;
			}
			/* check for weak store step */
			final Term storeIndex = checkStoreIndex(path[i], path[i + 1]);
			if (storeIndex != null) {
				// this is a step from a to (store a storeIndex v). Check if storeIndex is okay.
				if (weakIdx != null) {
					// for a weak path it needs to be different from weakIdx to prove a[weakIdx] = store[weakIdx]
					if (disequalities.contains(new SymmetricPair<>(weakIdx, storeIndex))
							|| checkTrivialDisequality(weakIdx, storeIndex)) {
						continue;
					}
				} else {
					// For the main path of the weakeq-ext lemma it must be one of the indices for which a weakPath was
					// given. For the main path of the const-weakeq lemma, we don't need to check the storeIndex.
					if (lemmaType.equals(":const-weakeq") || weakPaths.contains(storeIndex)) {
						continue;
					}
				}
			}
			/* check for select edge (only for weakeq-ext) */
			if (weakIdx != null && lemmaType.equals(":weakeq-ext")) {
				/*
				 * check for select path with select indices equal to weakIdx, both trivially equal and proven equal by
				 * a strong path
				 */
				if (checkSelectPath(pair, weakIdx, equalities)) {
					continue;
				}
			}
			reportError("unexplained equality " + path[i] + " == " + path[i + 1]);
		}
	}

	/**
	 * Checks whether there is a select edge that would explain a step in a weak path of the weakeq-ext lemma. Usually,
	 * this is a select equality {@code a[i] = b[j]} with {@code weakIdx = i} and {@code weakIdx = j}. This could also
	 * be a select-const equality {@code a[i] = v} when {@code b} is a const term {@code (const v)}.
	 *
	 * @param termPair
	 *            the pair a,b whose step should be explained.
	 * @param weakIdx
	 *            the index of the weak path.
	 * @param equalities
	 *            the equalities that occur negated in the lemma and can be used.
	 * @return true if the step is explained by a valid select edge or select-const edge.
	 */
	private boolean checkSelectPath(final SymmetricPair<Term> termPair, final Term weakIdx,
			final HashSet<SymmetricPair<Term>> equalities) {
		for (final SymmetricPair<Term> candidateEquality : equalities) {
			// Check for each candidate equality if it explains a select edge for a weakeq-ext lemma.
			// We check if termPair.first[weakIdx]] equals one side of the equality and termPair.second[weakIdx]
			// equals the other side.
			if (checkSelectConst(candidateEquality.getFirst(), termPair.getFirst(), weakIdx, equalities)
					&& checkSelectConst(candidateEquality.getSecond(), termPair.getSecond(), weakIdx, equalities)) {
				return true;
			}
			if (checkSelectConst(candidateEquality.getFirst(), termPair.getSecond(), weakIdx, equalities)
					&& checkSelectConst(candidateEquality.getSecond(), termPair.getFirst(), weakIdx, equalities)) {
				return true;
			}
		}
		// No candidate equality was found but it could also be a select-const edge where a[i] and v are
		// syntactically equal, in which case there is no equality.
		if (isApplication("const", termPair.getFirst())
				&& checkSelectConst(((ApplicationTerm) termPair.getFirst()).getParameters()[0], termPair.getSecond(),
						weakIdx, equalities)) {
			return true;
		}
		if (isApplication("const", termPair.getSecond())
				&& checkSelectConst(((ApplicationTerm) termPair.getSecond()).getParameters()[0], termPair.getFirst(),
						weakIdx, equalities)) {
			return true;
		}
		return false;
	}

	/**
	 * Check if array[weakIdx] is value, either because value is the select term, or array is a constant array on value.
	 */
	private boolean checkSelectConst(final Term value, final Term array, final Term weakIdx,
			final HashSet<SymmetricPair<Term>> strongPaths) {
		// Check if value is (select array idx2) with (weakIdx = idx2) in equalities or syntactically equal.
		if (isApplication("select", value)) {
			final Term[] args = ((ApplicationTerm) value).getParameters();
			if (args[0] == array
					&& (args[1] == weakIdx || strongPaths.contains(new SymmetricPair<>(args[1], weakIdx)))) {
				return true;
			}
		}
		// Check if array is (const value)
		if (isApplication("const", array) && ((ApplicationTerm) array).getParameters()[0] == value) {
			return true;
		}
		return false;
	}

	/**
	 * Checks whether {@code term1} is {@code (store term2 idx val)} or {@code term2} is {@code (store term1 idx val)}.
	 *
	 * @param term1
	 *            the first array term.
	 * @param term2
	 *            the second array term
	 * @return idx if one of the terms is a store term of the other, or null if not.
	 */
	private Term checkStoreIndex(final Term term1, final Term term2) {
		if (isApplication("store", term1)) {
			final Term[] storeArgs = ((ApplicationTerm) term1).getParameters();
			if (storeArgs[0] == term2) {
				return storeArgs[1];
			}
		}
		if (isApplication("store", term2)) {
			final Term[] storeArgs = ((ApplicationTerm) term2).getParameters();
			if (storeArgs[0] == term1) {
				return storeArgs[1];
			}
		}
		return null;
	}

	/**
	 * Checks if first and second are equal (modulo order of operands for +).
	 *
	 * @return true if first and second are equal.
	 */
	boolean checkTrivialEquality(final Term first, final Term second) {
		if (first == second) {
			return true;
		}
		if (!first.getSort().isNumericSort()) {
			return false;
		}
		final SMTAffineTerm diff = new SMTAffineTerm(second);
		diff.negate();
		diff.add(new SMTAffineTerm(first));
		return diff.isConstant() && diff.getConstant().equals(Rational.ZERO);
	}

	/**
	 * Check a data type lemma for correctness. If a problem is found, an error is
	 * reported.
	 *
	 * @param type         the lemma type
	 * @param clause       the clause to check
	 * @param ccAnnotation the argument of the :CC annotation.
	 */
	private void checkDataTypeLemma(final String type, final Term[] clause, final Object[] ccAnnotation) {
		// FIXME: add checks
		return;
	}

	/**
	 * Check whether the disequality between two terms is trivial. There are two
	 * cases, (1) the difference between the terms is constant and nonzero, e.g.
	 * {@code (= x (+ x 1))}, or (2) the difference contains only integer variables
	 * and the constant divided by the gcd of the factors is non-integral, e.g.,
	 * {@code (= (+ x (* 2 y)) (+ x (* 2 z) 1))}.
	 *
	 * @param first  the left-hand side of the equality
	 * @param second the right-hand side of the equality
	 * @return true if the equality is trivially not satisfied.
	 */
	boolean checkTrivialDisequality(final Term first, final Term second) {
		if (!first.getSort().isNumericSort()) {
			return false;
		}
		final SMTAffineTerm diff = new SMTAffineTerm(first);
		diff.add(Rational.MONE, second);
		if (diff.isConstant()) {
			return !diff.getConstant().equals(Rational.ZERO);
		} else {
			return diff.isAllIntSummands() && !diff.getConstant().div(diff.getGcd()).isIntegral();
		}
	}

	/**
	 * Check an LA lemma for correctness. If a problem is found, an error is reported.
	 *
	 * @param clause
	 *            the clause to check
	 * @param coefficients
	 *            the argument of the :LA annotation, which is the list of Farkas coefficients.
	 */
	private void checkLALemma(final Term[] clause, final Term[] coefficients) {
		if (clause.length != coefficients.length) {
			reportError("Clause and coefficients have different length");
			return;
		}
		if (clause.length == 0) {
			reportError("Empty LA lemma");
			return;
		}

		boolean sumHasStrict = false;
		final SMTAffineTerm sum = new SMTAffineTerm();
		for (int i = 0; i < clause.length; i++) {
			final Rational coeff = parseConstant(coefficients[i]);
			if (coeff == null) {
				reportError("Coefficient is not a constant.");
				return;
			}
			if (coeff.equals(Rational.ZERO)) {
				reportWarning("Coefficient in LA lemma is zero.");
				continue;
			}
			Term literal = clause[i];
			boolean isNegated = false;
			if (isApplication("not", literal)) {
				literal = ((ApplicationTerm) literal).getParameters()[0];
				isNegated = true;
			}
			literal = unquote(literal);
			boolean isStrict;
			if (isNegated) {
				if (isApplication("<=", literal)) {
					isStrict = false;
					if (coeff.isNegative()) {
						reportError("Negative coefficient for <=");
					}
				} else if (isApplication("=", literal)) {
					isStrict = false;
				} else if (isApplication("<", literal)) {
					isStrict = true;
					if (coeff.isNegative()) {
						reportError("Negative coefficient for <");
					}
				} else {
					reportError("Unknown atom in LA lemma: " + literal);
					continue;
				}
			} else {
				if (isApplication("<=", literal)) {
					isStrict = true;
					if (!coeff.isNegative()) {
						reportError("Positive coefficient for negated <=");
					}
				} else if (isApplication("<", literal)) {
					isStrict = false;
					if (!coeff.isNegative()) {
						reportError("Positive coefficient for negated <");
					}
				} else {
					reportError("Unknown atom in LA lemma: " + literal);
					continue;
				}
			}
			final Term[] params = ((ApplicationTerm) literal).getParameters();
			if (params.length != 2) {
				reportError("not a binary comparison in LA lemma");
				continue;
			}
			if (!isZero(params[1])) {
				reportError("Right hand side is not zero");
			}
			final SMTAffineTerm affine = new SMTAffineTerm(params[0]);
			if (isStrict && params[0].getSort().getName().equals("Int")) {
				/*
				 * make integer equalities non-strict by adding one. x < 0 iff x + 1 <= 0 and x > 0 iff x - 1 >= 0
				 */
				affine.add(isNegated ? Rational.ONE : Rational.MONE);
				isStrict = false;
			}
			affine.mul(coeff);
			sum.add(affine);
			sumHasStrict |= isStrict;
		}
		if (sum.isConstant()) {
			/*
			 * There is a contradiction (correct lemma) iff it sums up to "sum <(=) 0" with sum > 0 or to "0 < 0".
			 */
			final int signum = sum.getConstant().signum();
			if (signum > 0 || (sumHasStrict && signum == 0)) {
				return;
			}
		}
		reportError("LA lemma sums up to " + sum + (sumHasStrict ? " < 0" : " <= 0"));
	}

	/**
	 * Check an trichotomy lemma for correctness. If a problem is found, an error is reported.
	 *
	 * @param clause
	 *            the clause to check.
	 */
	private void checkTrichotomy(final Term[] clause) {
		if (clause.length != 3) { // NOCHECKSTYLE
			reportError("Malformed Trichotomy clause: " + Arrays.toString(clause));
			return;
		}

		SMTAffineTerm trichotomyTerm = null;
		final int NEQ = 1;
		final int LEQ = 2;
		final int GEQ = 4;
		int foundlits = 0;
		for (Term lit : clause) {
			final boolean isNegated = isApplication("not", lit);
			if (isNegated) {
				lit = ((ApplicationTerm) lit).getParameters()[0];
			}
			lit = unquote(lit);

			Rational offset = Rational.ZERO;
			if (isApplication("=", lit)) {
				if (isNegated) {
					reportError("Equality in trichotomy has wrong polarity");
					return;
				}
				if ((foundlits & NEQ) != 0) {
					reportError("Two Disequalities in trichotomy");
					return;
				}
				foundlits |= NEQ;
			} else if (isApplication("<=", lit)) {
				if (isNegated) {
					if ((foundlits & GEQ) != 0) {
						reportError("Two > in trichotomy");
						return;
					}
					foundlits |= GEQ;
				} else {
					if ((foundlits & LEQ) != 0) {
						reportError("Two <= in trichotomy");
						return;
					}
					foundlits |= LEQ;
					offset = Rational.MONE; // x <= 0 iff x - 1 < 0
				}
			} else if (isApplication("<", lit)) {
				if (isNegated) {
					if ((foundlits & GEQ) != 0) {
						reportError("Two >= in trichotomy");
						return;
					}
					foundlits |= GEQ;
					offset = Rational.ONE; // x >= 0 iff x + 1 > 0
				} else {
					if ((foundlits & LEQ) != 0) {
						reportError("Two < in trichotomy");
						return;
					}
					foundlits |= LEQ;
				}
			} else {
				reportError("Unknown literal in trichotomy " + lit);
				return;
			}
			final Term[] params = ((ApplicationTerm) lit).getParameters();
			if (params.length != 2) {
				reportError("not a binary comparison in LA lemma");
				return;
			}
			if (!isZero(params[1])) {
				reportError("Right hand side is not zero");
			}
			if (offset != Rational.ZERO && !params[1].getSort().getName().equals("Int")) {
				reportError("<= or >= in non-integer trichotomy");
			}
			final SMTAffineTerm affine = new SMTAffineTerm(params[0]);
			affine.add(offset);
			if (trichotomyTerm == null) {
				trichotomyTerm = affine;
			} else if (!trichotomyTerm.equals(affine)) {
				reportError("Invalid trichotomy");
			}
		}
		assert foundlits == (NEQ + LEQ + GEQ);
	}

	/**
	 * Check an EQ lemma for correctness. If a problem is found, an error is reported.
	 *
	 * @param clause
	 *            the clause to check
	 */
	private void checkEQLemma(final Term[] clause) {
		if (clause.length != 2) {
			reportError("Lemma :EQ must have two literals");
			return;
		}
		Term lit1 = clause[0];
		Term lit2 = clause[1];
		if (isApplication("not", lit1)) {
			lit1 = ((ApplicationTerm) lit1).getParameters()[0];
		} else if (isApplication("not", lit2)) {
			lit2 = ((ApplicationTerm) lit2).getParameters()[0];
		} else {
			reportError("Lemma :EQ must have one negated literal");
			return;
		}
		lit1 = unquote(lit1);
		lit2 = unquote(lit2);

		if (!isApplication("=", lit1) || ((ApplicationTerm) lit1).getParameters().length != 2
				|| !isApplication("=", lit2) || ((ApplicationTerm) lit2).getParameters().length != 2) {
			reportError("Lemma :EQ must have one equality and one disequality");
			return;
		}
		final Term[] lit1Args = ((ApplicationTerm) lit1).getParameters();
		final Term[] lit2Args = ((ApplicationTerm) lit2).getParameters();
		final SMTAffineTerm diff1 = new SMTAffineTerm(lit1Args[0]);
		diff1.add(Rational.MONE, lit1Args[1]);
		final SMTAffineTerm diff2 = new SMTAffineTerm(lit2Args[0]);
		diff2.add(Rational.MONE, lit2Args[1]);
		// check that they are not constant to avoid gcd errors.
		if (diff1.isConstant() || diff2.isConstant()) {
			reportError("Lemma :EQ with trivial equalities");
			return;
		}
		diff1.div(diff1.getGcd());
		diff2.div(diff2.getGcd());
		if (diff1.equals(diff2)) {
			return;
		}
		diff1.negate();
		if (diff1.equals(diff2)) {
			return;
		}
		reportError("Error in lemma :EQ");
	}

	private void checkInstLemma(final Term[] clause, final Object[] quantAnnotation) {
		// Check that the first literal in the lemma is a negated universally quantified literal.
		if (!isApplication("not", clause[0])) {
			reportError("Lemma :inst must contain negated forall-literal as first literal.");
			return;
		}
		final Term firstAtom = unquote(((ApplicationTerm) clause[0]).getParameters()[0]);
		if (!(firstAtom instanceof QuantifiedFormula) || ((QuantifiedFormula) firstAtom).getQuantifier() != 1) {
			reportError("First literal in lemma :inst must be universally quantified formula.");
			return;
		}

		// Check that the annotation of the lemma is well-formed.
		if (quantAnnotation.length != 5 || quantAnnotation[0] != ":subs" || !(quantAnnotation[1] instanceof Term[])
				|| (quantAnnotation[2] != ":conflict" && quantAnnotation[2] != ":e-matching"
						&& quantAnnotation[2] != ":enumeration")
				|| quantAnnotation[3] != ":subproof" || !(quantAnnotation[4] instanceof ApplicationTerm)) {
			reportError("Malformed QuantAnnotation.");
			return;
		}
		// Check that the annotation of the lemma contains a subproof for the lemma clause.
		final ApplicationTerm subproof = (ApplicationTerm) quantAnnotation[4];
		enqueueWalker(new InstLemmaWalker(clause, (Term[]) quantAnnotation[1]));
		enqueueWalker(new ProofWalker(subproof));
	}

	/* === Tautologies === */

	Term walkTautology(final ApplicationTerm tautologyApp) {
		/*
		 * Tautologies are created to define the meaning of proxy literals like (! (or a b c) :quoted), or of proxy
		 * terms like (ite cond t1 t2) or (div x 5). They are of the form
		 *
		 * (@tautology (! (or ...) :type))
		 *
		 * The possible types are defined in ProofConstants.AUX_*
		 */
		final String tautologyName = getSingleAnnotation(tautologyApp.getParameters()[0]).getKey();
		if (tautologyName == null) {
			reportError("Malformed tautology rule " + tautologyApp);
			return null;
		}
		final Term tautology = ((AnnotatedTerm) tautologyApp.getParameters()[0]).getSubterm();
		final Term[] clause = termToClause(tautology);

		boolean result;
		switch (tautologyName) {
		case ":trueNotFalse":
			result = (clause.length == 1 && clause[0] == mSkript.term("not",
					mSkript.term("=", mSkript.term("true"), mSkript.term("false"))));
			break;
		case ":or+":
			result = checkTautOrPos(clause);
			break;
		case ":or-":
			result = checkTautOrNeg(clause);
			break;
		case ":ite+1":
		case ":ite+2":
		case ":ite+red":
		case ":ite-1":
		case ":ite-2":
		case ":ite-red":
			result = checkTautIte(tautologyName, clause);
			break;
		case ":xor+1":
		case ":xor+2":
		case ":xor-1":
		case ":xor-2":
			result = checkTautXor(tautologyName, clause);
			break;
		case ":termITE":
			result = checkTautTermIte(clause);
			break;
		case ":termITEBound":
			result = checkTautTermIteBound(clause);
			break;
		case ":excludedMiddle1":
		case ":excludedMiddle2":
			result = checkTautExcludedMiddle(tautologyName, clause);
			break;
		case ":divHigh":
		case ":divLow":
		case ":toIntHigh":
		case ":toIntLow":
			result = checkTautLowHigh(tautologyName, clause);
			break;
		case ":store":
			result = checkTautStore(clause);
			break;
		case ":diff":
			result = checkTautDiff(clause);
			break;
		case ":matchCase":
		case ":matchDefault":
			result = true;
			reportWarning("Unchecked datatype tautology rule " + tautologyApp);
			break;
		default:
			result = false;
			break;
		}

		if (!result) {
			reportError("Malformed/unknown tautology rule " + tautologyApp);
		}

		return tautology;
	}

	private boolean checkTautOrPos(final Term[] clause) {
		// Check for the form: (or (not (! (or p1 ... pn) :quoted)) p1 ... pn)
		final Term lit = unquote(negate(clause[0]), true);
		if (!isApplication("or", lit) || ((ApplicationTerm) lit).getParameters().length != clause.length - 1) {
			return false;
		}
		final Term[] params = ((ApplicationTerm) lit).getParameters();
		for (int i = 0; i < params.length; i++) {
			if (params[i] != clause[i + 1]) {
				return false;
			}
		}
		return true;
	}

	private boolean checkTautOrNeg(final Term[] clause) {
		// Check for the form: (or (! (or p1 ... pn) :quoted) (not pi))
		if (clause.length != 2) {
			return false;
		}
		final Term lit = unquote(clause[0], true);
		if (!isApplication("or", lit)) {
			return false;
		}
		if (!isApplication("not", clause[1])) {
			return false;
		}
		final Term otherLit = ((ApplicationTerm) clause[1]).getParameters()[0];
		final ArrayDeque<Term> todo = new ArrayDeque<>();
		todo.addAll(Arrays.asList(((ApplicationTerm) lit).getParameters()));
		while (!todo.isEmpty()) {
			final Term t = todo.removeFirst();
			if (t == otherLit) {
				/* found it; everything okay */
				return true;
			}
			if (isApplication("or", t)) {
				/* descend into nested or */
				todo.addAll(Arrays.asList(((ApplicationTerm) t).getParameters()));
			}
		}
		return false;
	}

	private boolean checkTautIte(final String tautKind, final Term[] clause) {
		if (clause.length != 3) {
			return false;
		}
		Term lit = clause[0];
		final boolean negated = isApplication("not", lit);
		if (negated) {
			lit = negate(lit);
		}
		lit = unquote(lit, true);
		if (!isApplication("ite", lit)) {
			return false;
		}
		final Term[] iteParams = ((ApplicationTerm) lit).getParameters();
		switch (tautKind) {
		case ":ite+1":
			// (or (not (! (ite cond then else)) :quoted)) (not cond) then)
			return negated && clause[1] == mSkript.term("not", iteParams[0]) && clause[2] == iteParams[1];
		case ":ite+2":
			// (or (not (! (ite cond then else)) :quoted)) cond else)
			return negated && clause[1] == iteParams[0] && clause[2] == iteParams[2];
		case ":ite+red":
			return negated && clause[1] == iteParams[1] && clause[2] == iteParams[2];
		case ":ite-1":
			// (or (! (ite cond then else) :quoted) (not cond) (not then))
			return !negated && clause[1] == mSkript.term("not", iteParams[0])
					&& clause[2] == mSkript.term("not", iteParams[1]);
		case ":ite-2":
			// (or (! (ite cond then else) :quoted) cond (not else))
			return !negated && clause[1] == iteParams[0] && clause[2] == mSkript.term("not", iteParams[2]);
		case ":ite-red":
			return !negated && clause[1] == mSkript.term("not", iteParams[1])
					&& clause[2] == mSkript.term("not", iteParams[2]);
		}
		return false;
	}

	private boolean checkTautXor(final String tautKind, final Term[] clause) {
		if (clause.length != 3) {
			return false;
		}
		Term lit = clause[0];
		final boolean negated = isApplication("not", lit);
		if (negated) {
			lit = negate(lit);
		}
		lit = unquote(lit, true);
		if (!isApplication("xor", lit)) {
			return false;
		}
		final Term[] eqParams = ((ApplicationTerm) lit).getParameters();
		if (eqParams.length != 2) {
			return false;
		}
		switch (tautKind) {
		case ":xor+1":
			// (or (! (xor t1 t2) :quoted) t1 t2)
			return negated && clause[1] == eqParams[0] && clause[2] == eqParams[1];
		case ":xor+2":
			// (or (! (xor t1 t2) :quoted) (not t1) (not t2))
			return negated && clause[1] == mSkript.term("not", eqParams[0])
					&& clause[2] == mSkript.term("not", eqParams[1]);
		case ":xor-1":
			// (or (not (! (xor t1 t2) :quoted)) t1 (not t2))
			return !negated && clause[1] == eqParams[0] && clause[2] == mSkript.term("not", eqParams[1]);
		case ":xor-2":
			// (or (not (! (xor t1 t2) :quoted)) (not t1) t2)
			return !negated && clause[1] == mSkript.term("not", eqParams[0]) && clause[2] == eqParams[1];
		}
		return false;
	}

	private boolean checkTautTermIte(final Term[] clause) {
		if (clause.length < 2) {
			return false;
		}
		// Check for the form: (or (not c1) c2 (not c3) (= (ite c1 (ite c2 * (ite c3 x *)) *) x))
		final Term iteEq = clause[clause.length - 1];
		final Theory theory = iteEq.getTheory();
		if (!isApplication("=", iteEq)) {
			return false;
		}
		final Term[] eqParams = ((ApplicationTerm) iteEq).getParameters();
		if (eqParams.length != 2) {
			return false;
		}
		Term term = eqParams[0];
		for (int i = 0; i < clause.length - 1; i++) {
			if (!isApplication("ite", term)) {
				return false;
			}
			final Term[] iteParams = ((ApplicationTerm) term).getParameters();
			if (clause[i] == theory.term("not", iteParams[0])) {
				// descend into then branch
				term = iteParams[1];
			} else if (clause[i] == iteParams[0]) {
				// descend into else branch
				term = iteParams[2];
			} else {
				return false;
			}
		}
		// check right hand side of equality
		return term == eqParams[1];
	}

	private boolean checkTautTermIteBound(final Term[] clause) {
		// Check for the form: (<= (+ (ite c1 t1 t2) x) 0) where (+ ti x) must be constant and <= 0.
		// The ite can also be nested, i.e. (<= (+ (ite c1 (ite c2 t1 t2) (ite c3 t3 t4)) x) 0)
		// The ite can also be negated.
		// One of the (+ ti x) terms must be equal to 0.
		// The conditions ci can have arbitrary form.
		if (clause.length != 1 || !isApplication("<=", clause[0])) {
			return false;
		}
		final Term[] leqArgs = ((ApplicationTerm) clause[0]).getParameters();
		if (leqArgs.length != 2 || !isZero(leqArgs[1])) {
			return false;
		}
		final SMTAffineTerm sum = new SMTAffineTerm(leqArgs[0]);
		// find the ite term and check it.
		// we check each ite if the lemma works with it.
		boolean foundITE = false;
		entryLoop: for (final Map.Entry<Term, Rational> entry : sum.getSummands().entrySet()) {
			if (!isApplication("ite", entry.getKey()) || entry.getValue().abs() != Rational.ONE) {
				continue;
			}
			Term[] iteArgs = ((ApplicationTerm) entry.getKey()).getParameters();

			boolean zeroSeen = false;
			final ArrayDeque<Term> toCheck = new ArrayDeque<>();
			toCheck.add(iteArgs[2]);
			toCheck.add(iteArgs[1]);
			// Now check for each ti if replacing ti with (ite c t1 t2) in sum results a non-positive constant.
			while (!toCheck.isEmpty()) {
				Term candidate = toCheck.removeLast();
				while (isApplication("ite", candidate)) {
					// nested ite. push the second branch to toCheck queue, and check the first one.
					iteArgs = ((ApplicationTerm) candidate).getParameters();
					toCheck.addLast(iteArgs[2]);
					candidate = iteArgs[1];
				}

				// replace (ite c t e) with candidate in sum, by adding (- candidate (ite c t e)) * entry.getValue().
				final SMTAffineTerm sumWithCandidate = new SMTAffineTerm(candidate);
				sumWithCandidate.add(Rational.MONE, entry.getKey());
				sumWithCandidate.mul(entry.getValue());
				sumWithCandidate.add(sum);

				// Afterwards the literal should be <= 0, to make the clause true.
				if (!sumWithCandidate.isConstant() || sumWithCandidate.getConstant().signum() > 0) {
					continue entryLoop;
				}
				if (sumWithCandidate.getConstant().signum() == 0) {
					zeroSeen = true;
				}
			}
			// check that the bound is tight, i.e. one of the sums should be 0.
			if (zeroSeen) {
				foundITE = true;
				break;
			}
		}
		return foundITE;
	}

	private boolean checkTautLowHigh(final String ruleName, final Term[] clause) {
		if (clause.length != 1) {
			return false;
		}
		Term literal = clause[0];
		final boolean isToInt = ruleName.startsWith(":toInt");
		final boolean isHigh = ruleName.endsWith("High");
		// isLow: (<= (+ (- arg0) (* d candidate) ) 0)
		// aka. (>= (- arg0 (* d candidate)) 0)
		// isHigh: (not (<= (+ (- arg0) (* d candidate) |d|) 0)
		// aka. (< (- arg0 (* d candidate)) |d|)
		// where candidate is (div arg0 d) or (to_int arg0) and d is 1 for toInt.

		if (isHigh) {
			if (!isApplication("not", literal)) {
				return false;
			}
			literal = ((ApplicationTerm) literal).getParameters()[0];
		}
		if (!isApplication("<=", literal)) {
			return false;
		}
		final Term[] leArgs = ((ApplicationTerm) literal).getParameters();
		final SMTAffineTerm lhs = new SMTAffineTerm(leArgs[0]);
		if (!isZero(leArgs[1])) {
			return false;
		}
		if (leArgs[0].getSort().getName() != (isToInt ? "Real" : "Int")) {
			return false;
		}

		final String func = isToInt ? "to_int" : "div";
		// search for the toInt or div term; note that there can be several div terms in case of a nested div.
		for (final Term candidate : lhs.getSummands().keySet()) {
			if (isApplication(func, candidate)) {
				final Term[] args = ((ApplicationTerm) candidate).getParameters();
				// compute d
				final Rational d;
				SMTAffineTerm summand;
				if (isToInt) {
					d = Rational.ONE;
					summand = new SMTAffineTerm(candidate);
				} else {
					final SMTAffineTerm arg1 = new SMTAffineTerm(args[1]);
					if (!arg1.isConstant()) {
						return false;
					}
					d = arg1.getConstant();
					if (d.equals(Rational.ZERO)) {
						return false;
					}
					summand = new SMTAffineTerm(candidate);
					summand.mul(d);
				}
				// compute expected term and check that lhs equals it.
				final SMTAffineTerm expected = new SMTAffineTerm(args[0]);
				expected.negate();
				expected.add(summand);
				if (isHigh) {
					expected.add(d.abs());
				}
				if (lhs.equals(expected)) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean checkTautExcludedMiddle(final String name, final Term[] clause) {
		if (clause.length != 2) {
			return false;
		}
		final boolean isEqTrue = name == ":excludedMiddle1";
		// Check for the form: (or (! (= p true) :quoted) (not p)) :excludedMiddle1
		// or (or (! (= p false) :quoted) p) :excludedMiddle2
		final Term equality = unquote(clause[0], true);
		if (!isApplication("=", equality)) {
			return false;
		}
		final Term[] eqArgs = ((ApplicationTerm) equality).getParameters();
		Term lit = clause[1];
		if (isEqTrue) {
			if (!isApplication("not", lit)) {
				return false;
			}
			lit = negate(lit);
		}
		if (eqArgs.length != 2 || eqArgs[0] != lit || !isApplication(isEqTrue ? "true" : "false", eqArgs[1])) {
			return false;
		}
		return true;
	}

	/**
	 * Check an select over store lemma for correctness. If a problem is found, an error is reported.
	 *
	 * @param clause
	 *            the clause to check.
	 */
	private boolean checkTautStore(final Term[] clause) {
		// Store tautology have the form
		// (@tautology (! (= (select (store a i v) i) v) :store))
		if (clause.length == 1) {
			final Term eqlit = clause[0];
			if (isApplication("=", eqlit)) {
				final Term[] sides = ((ApplicationTerm) eqlit).getParameters();
				if (isApplication("select", sides[0])) {
					final ApplicationTerm select = (ApplicationTerm) sides[0];
					final Term store = select.getParameters()[0];
					if (isApplication("store", store)) {
						final Term[] storeArgs = ((ApplicationTerm) store).getParameters();
						if (storeArgs[1] == select.getParameters()[1] && storeArgs[2] == sides[1]) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	private boolean checkTautDiff(final Term[] clause) {
		if (clause.length != 2) {
			return false;
		}
		final Term arrEq = clause[0];
		final Term selectDisEq = clause[1];
		if (isApplication("not", selectDisEq)) {
			final Term selectEq = ((ApplicationTerm) selectDisEq).getParameters()[0];
			if (isApplication("=", arrEq) && isApplication("=", selectEq)) {
				final Term[] arrays = ((ApplicationTerm) arrEq).getParameters();
				final Term[] selects = ((ApplicationTerm) selectEq).getParameters();
				if (arrays.length == 2 && selects.length == 2 && isApplication("select", selects[0])
						&& isApplication("select", selects[1])) {
					boolean failure = false;
					for (int i = 0; i < 2; i++) {
						final Term[] selectArgs = ((ApplicationTerm) selects[i]).getParameters();
						if (selectArgs.length != 2 || selectArgs[0] != arrays[i]
								|| !isApplication("@diff", selectArgs[1])) {
							failure = true;
							break;
						}
						final Term[] diffArgs = ((ApplicationTerm) selectArgs[1]).getParameters();
						if (diffArgs.length != 2 || diffArgs[0] != arrays[0] || diffArgs[1] != arrays[1]) {
							failure = true;
							break;
						}
					}
					return !failure;
				}
			}
		}
		return false;
	}

	Term walkAsserted(final ApplicationTerm assertedApp) {
		final Term assertedTerm = assertedApp.getParameters()[0];
		if (!mAssertions.contains(assertedTerm)) {
			reportError("Could not find asserted term " + assertedTerm);
		}
		/* Just return the part without @asserted */
		return assertedTerm;
	}

	Term walkReflexivity(final ApplicationTerm reflexivityApp) {
		// sanity check (caller and typechecker should ensure this
		assert reflexivityApp.getFunction().getName() == ProofConstants.FN_REFL;
		assert reflexivityApp.getParameters().length == 1;

		// reflexivity (@refl term) proves (= term term).
		final Theory theory = reflexivityApp.getTheory();
		final Term term = reflexivityApp.getParameters()[0];
		final Term newEquality = theory.term("=", term, term);
		return newEquality;
	}

	Term walkTransitivity(final ApplicationTerm transitivityApp, final Term[] implications) {
		// sanity check (caller and typechecker should ensure this
		assert transitivityApp.getFunction().getName() == ProofConstants.FN_TRANS;

		Term firstTerm = null;
		Term lastTerm = null;
		boolean containsImplication = false;
		for (int i = 0; i < implications.length; i++) {
			if (isApplication("=>", implications[i])) {
				containsImplication = true;
			}
			// Check that subproofs prove equalities
			if (!isApplication("=", implications[i]) && !isApplication("=>", implications[i])
					|| ((ApplicationTerm) implications[i]).getParameters().length != 2) {
				// don't report errors if sub proof already failed
				if (implications[i] != null) {
					reportError("@trans on a proof of a non-equality or -implication: " + implications[i]);
				}
				return null;
			}
			final Term[] impParams = ((ApplicationTerm) implications[i]).getParameters();
			/* check that equalities chain correctly */
			if (i == 0) {
				firstTerm = impParams[0];
			} else if (impParams[0] != lastTerm) {
				reportError("@trans doesn't chain: " + lastTerm + " and " + impParams[0]);
			}
			lastTerm = impParams[1];
		}
		return transitivityApp.getTheory().term(containsImplication ? "=>" : "=", firstTerm, lastTerm);
	}

	Term walkCongruence(final ApplicationTerm congruenceApp, final Term[] subProofs) {
		// sanity check (caller and typechecker should ensure this
		assert congruenceApp.getFunction().getName() == ProofConstants.FN_CONG;
		for (int i = 0; i < subProofs.length; i++) {
			/* Check that it is an equality */
			if (!isApplication("=", subProofs[i]) || ((ApplicationTerm) subProofs[i]).getParameters().length != 2) {
				// don't report errors if sub proof already failed
				if (subProofs[i] != null) {
					reportError("@cong on a proof of a non-equality: " + subProofs[i]);
				}
				return null;
			}
		}
		/* assume that the first equality is of the form (= x (f p1 ... pn)) */
		final Term funcTerm = ((ApplicationTerm) subProofs[0]).getParameters()[1];
		if (!(funcTerm instanceof ApplicationTerm)) {
			reportError("@cong applied on a non-function term " + funcTerm);
			return null;
		}
		final Term[] funcParams = ((ApplicationTerm) funcTerm).getParameters();
		final Term[] newFuncParams = funcParams.clone();
		/* check that the rewrites are of the form (= pi qi) where the i's are increasing */
		int offset = 0;
		for (int i = 1; i < subProofs.length; i++) {
			final Term[] argRewrite = ((ApplicationTerm) subProofs[i]).getParameters();
			/* search the parameter that is rewritten */
			while (offset < funcParams.length && funcParams[offset] != argRewrite[0]) {
				offset++;
			}
			if (offset == funcParams.length) {
				reportError("cannot find rewritten parameter in @cong: " + subProofs[i] + " in " + funcTerm);
				offset = 0;
			} else {
				newFuncParams[offset] = argRewrite[1];
				offset++;
			}
		}
		/* compute the proven equality (= x (f q1 ... qn)) */
		final Theory theory = congruenceApp.getTheory();
		final Term newEquality = theory.term("=", ((ApplicationTerm) subProofs[0]).getParameters()[0],
				theory.term(((ApplicationTerm) funcTerm).getFunction(), newFuncParams));
		return newEquality;
	}

	Term walkOrMonotony(final ApplicationTerm orMonotonyApp, final Term[] subProofs) {
		// sanity check (caller and typechecker should ensure this
		assert orMonotonyApp.getFunction().getName() == ProofConstants.FN_ORMONOTONY;
		boolean containsImplication = false;
		for (int i = 0; i < subProofs.length; i++) {
			/* Check that it is an implication */
			if (!isApplication("=", subProofs[i]) && (i == 0 || !isApplication("=>", subProofs[i]))
					|| ((ApplicationTerm) subProofs[i]).getParameters().length != 2) {
				// don't report errors if sub proof already failed
				if (subProofs[i] != null) {
					reportError("@orMonotony on a proof that is not an implication: " + subProofs[i]);
				}
				return null;
			}
		}
		/* assume that the first equality is of the form (= x (f p1 ... pn)) */
		final Term orTerm = ((ApplicationTerm) subProofs[0]).getParameters()[1];
		if (!(orTerm instanceof ApplicationTerm)) {
			reportError("@orMonotony applied on a term that is not an or application: " + orTerm);
			return null;
		}

		final Term[] disjuncts = ((ApplicationTerm) orTerm).getParameters();
		final Term[] newDisjuncts = disjuncts.clone();
		/* check that the rewrites are of the form (=> pi qi) or (= pi qi) where the i's are increasing */
		int offset = 0;
		for (int i = 1; i < subProofs.length; i++) {
			if (isApplication("=>", subProofs[i])) {
				containsImplication = true;
			}
			final Term[] argRewrite = ((ApplicationTerm) subProofs[i]).getParameters();
			/* search the parameter that is rewritten */
			while (offset < disjuncts.length && disjuncts[offset] != argRewrite[0]) {
				offset++;
			}
			if (offset == disjuncts.length) {
				reportError("cannot find rewritten parameter in @orMonotony: " + subProofs[i] + " in " + orTerm);
				offset = 0;
			} else {
				newDisjuncts[offset] = argRewrite[1];
				offset++;
			}
		}
		/* compute the proven implication or equality (=> x (f q1 ... qn)) or (= x (f q1 ... qn)) */
		final Theory theory = orMonotonyApp.getTheory();
		final Term newImplication = theory.term(containsImplication ? "=>" : "=",
				((ApplicationTerm) subProofs[0]).getParameters()[0], theory.term("or", newDisjuncts));
		return newImplication;

	}

	Term walkExists(final ApplicationTerm existsApp, final Term subProof) {
		// sanity check (caller and typechecker should ensure this
		assert existsApp.getFunction().getName() == ProofConstants.FN_EXISTS;
		/* Check that subproof is an equality */
		if (!isApplication("=", subProof) || ((ApplicationTerm) subProof).getParameters().length != 2) {
			// don't report errors if sub proof already failed
			if (subProof != null) {
				reportError("@exists on a proof of a non-equality: " + subProof);
			}
			return null;
		}

		final AnnotatedTerm annotatedTerm = (AnnotatedTerm) existsApp.getParameters()[0];
		final Annotation varAnnot = annotatedTerm.getAnnotations()[0];
		if (annotatedTerm.getAnnotations().length != 1 || varAnnot.getKey() != ":vars"
				|| !(varAnnot.getValue() instanceof TermVariable[])) {
			reportError("@exists with malformed annotation: " + existsApp);
		}
		final TermVariable[] vars = (TermVariable[]) varAnnot.getValue();

		/* compute the proven equality (= (exists (...) lhs) (exists (...) rhs)) */
		final Term lhs = ((ApplicationTerm) subProof).getParameters()[0];
		final Term rhs = ((ApplicationTerm) subProof).getParameters()[1];
		final Theory theory = existsApp.getTheory();
		final Term newEquality = theory.term("=", theory.exists(vars, lhs), theory.exists(vars, rhs));
		return newEquality;
	}

	Term walkRewrite(final ApplicationTerm rewriteApp) {
		/*
		 * A rewrite rule has the form (@rewrite (! (= lhs rhs) :rewriteRule)) The rewriteRule gives the name of the
		 * rewrite axiom. The equality (= lhs rhs) is then a simple rewrite axiom.
		 *
		 * Exception: rewriteRule :removeForall has the form (@rewrite (! (=> lhs rhs) :removeForall)).
		 */
		assert rewriteApp.getFunction().getName() == ProofConstants.FN_REWRITE;
		assert rewriteApp.getParameters().length == 1;
		final Annotation annot = getSingleAnnotation(rewriteApp.getParameters()[0]);
		final String rewriteRule = annot.getKey();
		if (rewriteRule == null) {
			reportError("Malformed rewrite rule " + rewriteApp);
			return null;
		}
		final Term rewriteStmt = ((AnnotatedTerm) rewriteApp.getParameters()[0]).getSubterm();
		if (rewriteRule != ":removeForall" && !isApplication("=", rewriteStmt)) {
			reportError("Equality rewrite rule is not a binary equality: " + rewriteApp);
			return null;
		}
		if (rewriteRule == ":removeForall" && !isApplication("=>", rewriteStmt)) {
			reportError("Implication rewrite rule is not a binary implication: " + rewriteApp);
			return null;
		}
		final Term[] stmtParams = ((ApplicationTerm) rewriteStmt).getParameters();
		if (stmtParams.length != 2) {
			reportError("Rewrite rule is not a binary equality or implication: " + rewriteApp);
			return null;
		}

		boolean okay;
		switch (rewriteRule) {
		case ":expand":
			okay = checkRewriteExpand(stmtParams[0], stmtParams[1]);
			break;
		case ":expandDef":
			okay = checkRewriteExpandDef(stmtParams[0], stmtParams[1]);
			break;
		case ":trueNotFalse":
			okay = checkRewriteTrueNotFalse(stmtParams[0], stmtParams[1]);
			break;
		case ":constDiff":
			okay = checkRewriteConstDiff(stmtParams[0], stmtParams[1]);
			break;
		case ":eqTrue":
		case ":eqFalse":
			okay = checkRewriteEqTrueFalse(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":eqSimp":
		case ":eqSame":
			okay = checkRewriteEqSimp(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":eqBinary":
			okay = checkRewriteEqBinary(stmtParams[0], stmtParams[1]);
			break;
		case ":distinctBool":
		case ":distinctSame":
		case ":distinctBinary":
			okay = checkRewriteDistinct(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":xorTrue":
		case ":xorFalse":
			okay = checkRewriteXorConst(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":xorNot":
			okay = checkRewriteXorNot(stmtParams[0], stmtParams[1]);
			break;
		case ":xorSame":
			okay = checkRewriteXorSame(stmtParams[0], stmtParams[1]);
			break;
		case ":notSimp":
			okay = checkRewriteNot(stmtParams[0], stmtParams[1]);
			break;
		case ":orSimp":
			okay = checkRewriteOrSimp(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":orTaut":
			okay = checkRewriteOrTaut(stmtParams[0], stmtParams[1]);
			break;
		case ":iteTrue":
		case ":iteFalse":
		case ":iteSame":
		case ":iteBool1":
		case ":iteBool2":
		case ":iteBool3":
		case ":iteBool4":
		case ":iteBool5":
		case ":iteBool6":
			okay = checkRewriteIte(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":andToOr":
			okay = checkRewriteAndToOr(stmtParams[0], stmtParams[1]);
			break;
		case ":eqToXor":
		case ":distinctToXor":
			okay = checkRewriteToXor(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":impToOr":
			okay = checkRewriteImpToOr(stmtParams[0], stmtParams[1]);
			break;
		case ":strip":
			okay = checkRewriteStrip(stmtParams[0], stmtParams[1]);
			break;
		case ":canonicalSum":
			okay = checkRewriteCanonicalSum(stmtParams[0], stmtParams[1]);
			break;
		case ":leqToLeq0":
		case ":ltToLeq0":
		case ":geqToLeq0":
		case ":gtToLeq0":
			okay = checkRewriteToLeq0(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":leqTrue":
		case ":leqFalse":
			okay = checkRewriteLeq(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":divisible":
			okay = checkRewriteDivisible(stmtParams[0], stmtParams[1]);
			break;
		case ":div1":
		case ":div-1":
		case ":divConst":
			okay = checkRewriteDiv(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":modulo1":
		case ":modulo-1":
		case ":moduloConst":
		case ":modulo":
			okay = checkRewriteModulo(rewriteRule, stmtParams[0], stmtParams[1]);
			break;
		case ":toInt":
			okay = checkRewriteToInt(stmtParams[0], stmtParams[1]);
			break;
		case ":storeOverStore":
			okay = checkRewriteStoreOverStore(stmtParams[0], stmtParams[1]);
			break;
		case ":selectOverStore":
			okay = checkRewriteSelectOverStore(stmtParams[0], stmtParams[1]);
			break;
		case ":flatten":
			okay = checkRewriteFlatten(stmtParams[0], stmtParams[1]);
			break;
		case ":storeRewrite":
			okay = checkRewriteStore(stmtParams[0], stmtParams[1]);
			break;
		case ":intern":
			okay = checkRewriteIntern(stmtParams[0], stmtParams[1]);
			break;
		case ":forallExists":
			okay = checkRewriteForallExists(stmtParams[0], stmtParams[1]);
			break;
		case ":skolem":
			okay = checkRewriteSkolem(stmtParams[0], stmtParams[1], (Term[]) annot.getValue());
			break;
		case ":removeForall":
			okay = checkRewriteRemoveForall(stmtParams[0], stmtParams[1], (Term[]) annot.getValue());
			break;
		default:
			okay = false;
			break;
		}

		if (!okay) {
			reportError("Malformed/unknown @rewrite rule " + rewriteApp);
		}

		/*
		 * The result is simply the equality (without annotation).
		 */
		return rewriteStmt;
	}

	boolean checkRewriteAndToOr(final Term lhs, final Term rhs) {
		// expect lhs: (and ...), rhs: (not (or (not ...)))
		if (!isApplication("and", lhs) || !isApplication("not", rhs)) {
			return false;
		}
		final Term orTerm = ((ApplicationTerm) rhs).getParameters()[0];
		if (!isApplication("or", orTerm)) {
			return false;
		}
		final Term[] andParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] orParams = ((ApplicationTerm) orTerm).getParameters();
		if (andParams.length != orParams.length) {
			return false;
		}
		for (int i = 0; i < andParams.length; i++) {
			if (orParams[i] != mSkript.term("not", andParams[i])) {
				return false;
			}
		}
		return true;
	}

	boolean checkRewriteImpToOr(final Term lhs, final Term rhs) {
		// expect lhs: (=> p1 ... pn), rhs: (or pn (not p1) .. (not pn-1))))
		if (!isApplication("=>", lhs) || !isApplication("or", rhs)) {
			return false;
		}
		final Term[] impParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] orParams = ((ApplicationTerm) rhs).getParameters();
		if (impParams.length != orParams.length) {
			return false;
		}
		for (int i = 0; i < impParams.length - 1; i++) {
			if (orParams[i + 1] != mSkript.term("not", impParams[i])) {
				return false;
			}
		}
		return orParams[0] == impParams[impParams.length - 1];
	}

	boolean checkRewriteToXor(final String rule, final Term lhs, Term rhs) {
		// expect lhs: (=/distinct a b), rhs: (not? (xor a b))
		if (!isApplication(rule == ":eqToXor" ? "=" : "distinct", lhs)) {
			return false;
		}
		if (rule == ":eqToXor") {
			rhs = negate(rhs);
		}
		if (!isApplication("xor", rhs)) {
			return false;
		}
		final Term[] eqParams = ((ApplicationTerm) lhs).getParameters();
		final Term[] xorParams = ((ApplicationTerm) rhs).getParameters();
		if (xorParams.length != 2 || eqParams.length != 2) {
			return false;
		}
		return xorParams[0] == eqParams[0] && xorParams[1] == eqParams[1];
	}

	boolean checkRewriteStrip(final Term lhs, final Term rhs) {
		// expect lhs: (! (...) :...), rhs: ...
		return (lhs instanceof AnnotatedTerm) && rhs == ((AnnotatedTerm) lhs).getSubterm();
	}

	boolean checkRewriteTrueNotFalse(final Term lhs, final Term rhs) {
		// expect lhs: (= ... true ... false ...)), rhs: false
		if (!isApplication("=", lhs) || !isApplication("false", rhs)) {
			return false;
		}
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		boolean foundTrue = false, foundFalse = false;
		for (final Term t : lhsParams) {
			if (isApplication("true", t)) {
				foundTrue = true;
			}
			if (isApplication("false", t)) {
				foundFalse = true;
			}
		}
		return foundTrue && foundFalse;
	}

	boolean checkRewriteConstDiff(final Term lhs, final Term rhs) {
		// lhs: (= ... 5 ... 7 ...), rhs: false
		if (!isApplication("=", lhs) || !isApplication("false", rhs)) {
			return false;
		}
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		if (!lhsParams[0].getSort().isNumericSort()) {
			return false;
		}
		Rational lastConstant = null;
		for (final Term t : lhsParams) {
			final Rational value = parseConstant(t);
			if (value != null) {
				if (lastConstant == null) {
					lastConstant = value;
				} else if (!lastConstant.equals(value)) {
					return true;
				}
			}
		}
		return false;
	}

	boolean checkRewriteEqTrueFalse(final String rewriteRule, final Term lhs, Term rhs) {
		// lhs: (= l1 true ln), rhs: (not (or (not l1) ... (not ln)))
		// duplicated entries in lhs should be removed in rhs.
		final boolean trueCase = rewriteRule.equals(":eqTrue");
		if (!isApplication("=", lhs)) {
			return false;
		}
		boolean found = false;
		final LinkedHashSet<Term> args = new LinkedHashSet<>();
		for (final Term t : ((ApplicationTerm) lhs).getParameters()) {
			if (trueCase && isApplication("true", t)) {
				found = true;
			} else if (!trueCase && isApplication("false", t)) {
				found = true;
			} else {
				args.add(t);
			}
		}
		if (!found) {
			return false;
		}
		if (args.size() == 1) {
			// special case for only one argument:
			// (= true x) --> x
			// (= false x) --> (not x)
			final Term x = args.iterator().next();
			return trueCase ? rhs == x : rhs == mSkript.term("not", x);
		} else {
			if (!isApplication("not", rhs)) {
				return false;
			}
			rhs = negate(rhs);
			if (!isApplication("or", rhs)) {
				return false;
			}
			final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
			if (rhsArgs.length != args.size()) {
				return false;
			}
			int i = 0;
			for (final Term t : args) {
				if (rhsArgs[i] != (trueCase ? mSkript.term("not", t) : t)) {
					return false;
				}
				i++;
			}
			return true;
		}
	}

	boolean checkRewriteEqSimp(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (= ...), rhs: (= ...) or true, if all entries in rhs are the same.
		// duplicated entries in lhs should be removed in rhs.
		if (!isApplication("=", lhs)) {
			return false;
		}
		final LinkedHashSet<Term> args = new LinkedHashSet<>();
		for (final Term t : ((ApplicationTerm) lhs).getParameters()) {
			args.add(t);
		}
		if (args.size() == 1) {
			return rewriteRule.equals(":eqSame") && isApplication("true", rhs);
		} else {
			if (!rewriteRule.equals(":eqSimp")) {
				return false;
			}
			if (!isApplication("=", rhs)) {
				return false;
			}
			final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
			if (rhsArgs.length != args.size()) {
				return false;
			}
			int i = 0;
			for (final Term t : args) {
				if (rhsArgs[i] != t) {
					return false;
				}
				i++;
			}
			return true;
		}
	}

	boolean checkRewriteEqBinary(final Term lhs, Term rhs) {
		// eqBinary is like expand (chainable) combined with andToOr
		if (!isApplication("=", lhs)) {
			return false;
		}
		final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
		if (lhsParams.length < 3) {
			return false;
		}
		if (!isApplication("not", rhs)) {
			return false;
		}
		rhs = ((ApplicationTerm) rhs).getParameters()[0];
		if (!isApplication("or", rhs)) {
			return false;
		}
		final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
		if (lhsParams.length != rhsParams.length + 1) {
			return false;
		}
		for (int i = 0; i < rhsParams.length; i++) {
			if (rhsParams[i] != mSkript.term("not", mSkript.term("=", lhsParams[i], lhsParams[i + 1]))) {
				return false;
			}
		}
		return true;
	}

	boolean checkRewriteOrSimp(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (or ...), rhs: (or ...)
		// duplicated entries in lhs and false should be removed in rhs.
		// if only one entry remains, or is omitted, if no entry remains, false is returned.
		if (!isApplication("or", lhs)) {
			return false;
		}
		final LinkedHashSet<Term> args = new LinkedHashSet<>();
		for (final Term t : ((ApplicationTerm) lhs).getParameters()) {
			if (!isApplication("false", t)) {
				args.add(t);
			}
		}
		if (args.isEmpty()) {
			return isApplication("false", rhs);
		} else if (args.size() == 1) {
			return rhs == args.iterator().next();
		} else {
			if (!isApplication("or", rhs)) {
				return false;
			}
			final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
			if (rhsArgs.length != args.size()) {
				return false;
			}
			int i = 0;
			for (final Term t : args) {
				if (rhsArgs[i] != t) {
					return false;
				}
				i++;
			}
			return true;
		}
	}

	boolean checkRewriteOrTaut(final Term lhs, final Term rhs) {
		if (!isApplication("or", lhs) || !isApplication("true", rhs)) {
			return false;
		}
		// case 1
		// lhs: (or ... true ...), rhs: true
		// case 2
		// lhs: (or ... p ... (not p) ...), rhs: true
		final HashSet<Term> seen = new HashSet<>();
		for (final Term t : ((ApplicationTerm) lhs).getParameters()) {
			if (isApplication("true", t)) {
				return true;
			}
			if (seen.contains(negate(t))) {
				return true;
			}
			seen.add(t);
		}

		return false;
	}

	boolean checkRewriteIte(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (ite cond then else)
		if (!isApplication("ite", lhs)) {
			return false;
		}
		final Term[] args = ((ApplicationTerm) lhs).getParameters();
		final Term cond = args[0];
		final Term t1 = args[1];
		final Term t2 = args[2];
		switch (rewriteRule) {
		case ":iteTrue":
			// (= (ite true t1 t2) t1)
			return isApplication("true", cond) && rhs == t1;
		case ":iteFalse":
			// (= (ite false t1 t2) t2)
			return isApplication("false", cond) && rhs == t2;
		case ":iteSame":
			// (= (ite cond t1 t1) t1)
			return t1 == t2 && rhs == t1;
		case ":iteBool1":
			// (= (ite cond true false) cond)
			return isApplication("true", t1) && isApplication("false", t2) && rhs == cond;
		case ":iteBool2":
			// (= (ite cond false true) (not cond))
			return isApplication("false", t1) && isApplication("true", t2) && rhs == mSkript.term("not", cond);
		case ":iteBool3":
			// (= (ite cond true t2) (or cond t2))
			return isApplication("true", t1) && rhs == mSkript.term("or", cond, t2);
		case ":iteBool4":
			// (= (ite cond false t2) (not (or cond (not t2))))
			return isApplication("false", t1)
					&& rhs == mSkript.term("not", mSkript.term("or", cond, mSkript.term("not", t2)));
		case ":iteBool5":
			// (= (ite cond t1 true) (or (not cond) t1))
			return isApplication("true", t2) && rhs == mSkript.term("or", mSkript.term("not", cond), t1);
		case ":iteBool6":
			// (= (ite cond t1 false) (not (or (not cond) (not t1))))
			return isApplication("false", t2) && rhs == mSkript.term("not",
					mSkript.term("or", mSkript.term("not", cond), mSkript.term("not", t1)));
		}
		return false;
	}

	boolean checkRewriteDistinct(final String rewriteRule, final Term lhs, Term rhs) {
		// lhs: (ite cond then else)
		if (!isApplication("distinct", lhs)) {
			return false;
		}
		final Term[] args = ((ApplicationTerm) lhs).getParameters();
		switch (rewriteRule) {
		case ":distinctBool":
			return args.length > 2 && args[0].getSort().getName() == "Bool" && isApplication("false", rhs);
		case ":distinctSame": {
			// (distinct ... x ... x ...) = false
			final HashSet<Term> seen = new HashSet<>();
			for (final Term t : args) {
				// If seen already contains the term we found the duplicate
				if (!seen.add(t)) {
					return isApplication("false", rhs);
				}
			}
			return false;
		}
		case ":distinctBinary": {
			rhs = negate(rhs);
			if (args.length == 2) {
				return rhs == mSkript.term("=", args[0], args[1]);
			}
			if (!isApplication("or", rhs)) {
				return false;
			}
			final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
			int offset = 0;
			for (int i = 0; i < args.length - 1; i++) {
				for (int j = i + 1; j < args.length; j++) {
					if (offset >= rhsArgs.length || rhsArgs[offset] != mSkript.term("=", args[i], args[j])) {
						return false;
					}
					offset++;
				}
			}
			return offset == rhsArgs.length;
		}
		}
		return false;
	}

	boolean checkRewriteXorConst(final String rewriteRule, final Term lhs, final Term rhs) {
		// lhs: (xor true/false arg1) or (xor arg0 true/false)
		if (!isApplication("xor", lhs)) {
			return false;
		}
		final Term[] args = ((ApplicationTerm) lhs).getParameters();
		switch (rewriteRule) {
		case ":xorTrue":
			return (isApplication("true", args[0]) && rhs == mSkript.term("not", args[1]))
					|| (isApplication("true", args[1]) && rhs == mSkript.term("not", args[0]));
		case ":xorFalse":
			return (isApplication("false", args[0]) && rhs == args[1])
					|| (isApplication("false", args[1]) && rhs == args[0]);
		default:
			return false;
		}
	}

	boolean checkRewriteXorNot(final Term lhs, Term rhs) {
		// lhs: (xor (not? arg0) (not? arg1)), rhs: (not? (xor arg0 arg1))
		boolean polarity = true;
		if (isApplication("not", rhs)) {
			polarity = !polarity;
			rhs = ((ApplicationTerm) rhs).getParameters()[0];
		}
		if (!isApplication("xor", lhs) || !isApplication("xor", rhs)) {
			return false;
		}
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
		if (lhsArgs.length != rhsArgs.length) {
			return false;
		}
		for (int i = 0; i < lhsArgs.length; i++) {
			// If lhsArg contains not, remove it, and switch polarity.
			// Then check it equals the corresponding rhsArg
			Term lhsArg = lhsArgs[i];
			if (isApplication("not", lhsArg)) {
				polarity = !polarity;
				lhsArg = ((ApplicationTerm) lhsArg).getParameters()[0];
			}
			if (lhsArg != rhsArgs[i]) {
				return false;
			}
		}
		// The lemma is well-formed if polarity is true, i.e., all nots cancel out.
		return polarity;
	}

	boolean checkRewriteXorSame(final Term lhs, final Term rhs) {
		if (!isApplication("xor", lhs)) {
			return false;
		}
		final Term[] lhsArgs = ((ApplicationTerm) lhs).getParameters();
		return lhsArgs.length == 2 && lhsArgs[0] == lhsArgs[1] && isApplication("false", rhs);
	}

	boolean checkRewriteNot(Term lhs, final Term rhs) {
		// lhs: (ite cond then else)
		if (!isApplication("not", lhs)) {
			return false;
		}
		lhs = ((ApplicationTerm) lhs).getParameters()[0];
		if (isApplication("false", lhs)) {
			return isApplication("true", rhs);
		}
		if (isApplication("true", lhs)) {
			return isApplication("false", rhs);
		}
		if (isApplication("not", lhs)) {
			return rhs == ((ApplicationTerm) lhs).getParameters()[0];
		}
		return false;
	}

	boolean checkRewriteCanonicalSum(final Term lhs, final Term rhs) {
		SMTAffineTerm expected;
		if (lhs instanceof ConstantTerm) {
			expected = new SMTAffineTerm(lhs);
		} else if (lhs instanceof ApplicationTerm) {
			final ApplicationTerm lhsApp = (ApplicationTerm) lhs;
			final Term[] lhsArgs = lhsApp.getParameters();
			switch (lhsApp.getFunction().getName()) {
			case "+":
				expected = new SMTAffineTerm(lhsArgs[0]);
				for (int i = 1; i < lhsArgs.length; i++) {
					expected.add(new SMTAffineTerm(lhsArgs[i]));
				}
				break;
			case "-":
				expected = new SMTAffineTerm(lhsArgs[0]);
				if (lhsArgs.length == 1) {
					expected.negate();
				} else {
					for (int i = 1; i < lhsArgs.length; i++) {
						final SMTAffineTerm arg = new SMTAffineTerm(lhsArgs[i]);
						arg.negate();
						expected.add(arg);
					}
				}
				break;
			case "*":
				expected = new SMTAffineTerm(lhsArgs[0]);
				for (int i = 1; i < lhsArgs.length; i++) {
					if (expected.isConstant()) {
						final Rational factor = expected.getConstant();
						expected = new SMTAffineTerm(lhsArgs[i]);
						expected.mul(factor);
					} else {
						final Rational factor = parseConstant(lhsArgs[i]);
						if (factor == null) {
							return false;
						}
						expected.mul(factor);
					}
				}
				break;
			case "/":
				expected = new SMTAffineTerm(lhsArgs[0]);
				for (int i = 1; i < lhsArgs.length; i++) {
					final Rational factor = parseConstant(lhsArgs[i]);
					if (factor == null) {
						return false;
					}
					expected.div(factor);
				}
				break;
			case "to_real":
				expected = new SMTAffineTerm(lhsArgs[0]);
				break;
			default:
				return false;
			}
		} else {
			return false;
		}
		final SMTAffineTerm rhsAffine = new SMTAffineTerm(rhs);
		return expected.equals(rhsAffine);
	}

	boolean checkRewriteFlatten(final Term lhs, final Term rhs) {
		// lhs: (or ... (or ...) ... ), rhs: (or ... ... ...)
		if (!isApplication("or", lhs) || !isApplication("or", rhs)) {
			return false;
		}
		final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
		int rhsOffset = 0;
		final ArrayDeque<Term> lhsArgs = new ArrayDeque<>();
		for (final Term t : ((ApplicationTerm) lhs).getParameters()) {
			lhsArgs.add(t);
		}
		while (!lhsArgs.isEmpty()) {
			final Term first = lhsArgs.removeFirst();
			if (rhsOffset >= rhsArgs.length) {
				return false;
			}
			if (rhsArgs[rhsOffset] == first) {
				rhsOffset++;
			} else {
				if (!isApplication("or", first)) {
					return false;
				}
				final Term[] args = ((ApplicationTerm) first).getParameters();
				for (int i = args.length - 1; i >= 0; i--) {
					lhsArgs.addFirst(args[i]);
				}
			}
		}
		return rhsOffset == rhsArgs.length;
	}

	boolean checkRewriteDivisible(final Term lhs, final Term rhs) {
		// ((_ divisible n) x) --> (= x (* n (div x n)))
		if (!isApplication("divisible", lhs)) {
			return false;
		}
		BigInteger num1;
		try {
			num1 = new BigInteger(((ApplicationTerm) lhs).getFunction().getIndices()[0]);
		} catch (final NumberFormatException e) {
			throw new SMTLIBException("index must be numeral", e);
		}
		final Rational num = Rational.valueOf(num1, BigInteger.ONE);
		if (num.equals(Rational.ONE)) {
			return isApplication("true", rhs);
		}
		final Term arg = ((ApplicationTerm) lhs).getParameters()[0];
		if (arg instanceof ConstantTerm) {
			final Rational value = SMTAffineTerm.convertConstant((ConstantTerm) arg);
			final boolean divisible = value.denominator().equals(BigInteger.ONE)
					&& value.numerator().mod(num.numerator()).equals(BigInteger.ZERO);
			return isApplication(divisible ? "true" : "false", rhs);
		}
		final Theory theory = lhs.getTheory();
		final Term numTerm = num.toTerm(arg.getSort());
		final Term expected = theory.term("*", numTerm, theory.term("div", arg, numTerm));
		if (!isApplication("=", rhs)) {
			return false;
		}
		final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
		return rhsArgs[0] == arg && rhsArgs[1] == expected;
	}

	private Rational divConst(final Rational dividend, final Rational divisor) {
		if (divisor.signum() > 0) {
			return dividend.div(divisor).floor();
		} else {
			return dividend.div(divisor.negate()).floor().negate();
		}
	}

	boolean checkRewriteDiv(final String ruleName, final Term lhs, final Term rhs) {
		// div1: (div x 1) -> x
		// div-1: (div x (- 1)) -> (- x)
		// divConst: (div c1 c2) -> c where c1,c2 are constants, c = (div c1 c2)
		if (!isApplication("div", lhs)) {
			return false;
		}
		final Term[] divArgs = ((ApplicationTerm) lhs).getParameters();
		if (divArgs.length != 2) {
			return false;
		}
		final Rational divisor = parseConstant(divArgs[1]);
		if (divisor == null) {
			return false;
		}

		switch (ruleName) {
		case ":div1":
			return divisor.equals(Rational.ONE) && rhs == divArgs[0];
		case ":div-1": {
			final SMTAffineTerm dividend = new SMTAffineTerm(divArgs[0]);
			final SMTAffineTerm quotient = new SMTAffineTerm(rhs);
			dividend.negate();
			return divisor.equals(Rational.MONE) && quotient.equals(dividend);
		}
		case ":divConst": {
			final Rational dividend = parseConstant(divArgs[0]);
			final Rational quotient = parseConstant(rhs);
			if (dividend == null || quotient == null) {
				return false;
			}
			return quotient.equals(divConst(dividend, divisor));
		}
		default:
			return false;
		}
	}

	boolean checkRewriteModulo(final String ruleName, final Term lhs, final Term rhs) {
		// mod1: (div x 1) -> 0
		// mod-1: (div x (- 1)) -> 0
		// moduloConst: (mod c1 c2) -> c where c1,c2 are constants, c = (mod c1 c2)
		// modulo: (mod x c) -> (- x (* c (div x c)))
		if (!isApplication("mod", lhs)) {
			return false;
		}
		final Term[] modArgs = ((ApplicationTerm) lhs).getParameters();
		if (modArgs.length != 2) {
			return false;
		}
		if (!(modArgs[1] instanceof ConstantTerm)) {
			return false;
		}
		final Rational divisor = SMTAffineTerm.convertConstant((ConstantTerm) modArgs[1]);
		switch (ruleName) {
		case ":modulo1":
			return divisor.equals(Rational.ONE) && isZero(rhs);
		case ":modulo-1":
			return divisor.equals(Rational.MONE) && isZero(rhs);
		case ":moduloConst": {
			final Rational dividend = parseConstant(modArgs[0]);
			final Rational quotient = parseConstant(rhs);
			if (dividend == null || quotient == null) {
				return false;
			}
			return quotient.equals(dividend.sub(divisor.mul(divConst(dividend, divisor))));
		}
		case ":modulo": {
			final Term divTerm = lhs.getTheory().term("div", modArgs);
			final SMTAffineTerm expected = new SMTAffineTerm(divTerm);
			expected.mul(divisor.negate());
			expected.add(new SMTAffineTerm(modArgs[0]));
			return new SMTAffineTerm(rhs).equals(expected);
		}
		default:
			return false;
		}
	}

	boolean checkRewriteToInt(final Term lhs, final Term rhs) {
		// (to_int constant) --> floor(constant)
		if (!isApplication("to_int", lhs)) {
			return false;
		}
		final Term arg = ((ApplicationTerm) lhs).getParameters()[0];
		final Rational argConst = parseConstant(arg);
		final Rational rhsConst = parseConstant(rhs);
		return argConst != null && rhsConst != null && rhsConst.equals(argConst.floor());
	}

	boolean checkRewriteExpand(final Term lhs, final Term rhs) {
		if (!(lhs instanceof ApplicationTerm)) {
			return false;
		}
		final ApplicationTerm at = ((ApplicationTerm) lhs);
		final FunctionSymbol f = at.getFunction();
		if (f.isLeftAssoc()) {
			final Term[] lhsParams = at.getParameters();
			if (lhsParams.length < 3) {
				return false;
			}
			Term right = rhs;
			for (int i = lhsParams.length - 1; i >= 1; i--) {
				if (!(right instanceof ApplicationTerm)) {
					return false;
				}
				final ApplicationTerm rightApp = (ApplicationTerm) right;
				if (rightApp.getFunction() != f || rightApp.getParameters().length != 2
						|| rightApp.getParameters()[1] != lhsParams[i]) {
					return false;
				}
				right = rightApp.getParameters()[0];
			}
			return right == lhsParams[0];
		} else if (f.isRightAssoc()) {
			final Term[] lhsParams = at.getParameters();
			if (lhsParams.length < 3) {
				return false;
			}
			Term right = rhs;
			for (int i = 0; i < lhsParams.length - 1; i++) {
				if (!(right instanceof ApplicationTerm)) {
					return false;
				}
				final ApplicationTerm rightApp = (ApplicationTerm) right;
				if (rightApp.getFunction() != f || rightApp.getParameters().length != 2
						|| rightApp.getParameters()[0] != lhsParams[i]) {
					return false;
				}
				right = rightApp.getParameters()[1];
			}
			return right == lhsParams[lhsParams.length - 1];
		} else if (f.isChainable()) {
			final Term[] lhsParams = at.getParameters();
			if (lhsParams.length < 3) {
				return false;
			}
			if (!isApplication("and", rhs)) {
				return false;
			}
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			if (lhsParams.length != rhsParams.length + 1) {
				return false;
			}
			for (int i = 0; i < rhsParams.length; i++) {
				if (!(rhsParams[i] instanceof ApplicationTerm)) {
					return false;
				}
				final ApplicationTerm rightApp = (ApplicationTerm) rhsParams[i];
				if (rightApp.getFunction() != f || rightApp.getParameters().length != 2
						|| rightApp.getParameters()[0] != lhsParams[i]
						|| rightApp.getParameters()[1] != lhsParams[i + 1]) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	boolean checkRewriteExpandDef(final Term lhs, final Term rhs) {
		// (= f arg) is expanded to (let ((var arg)) body), if f has definition body.
		if (!(lhs instanceof ApplicationTerm)) {
			return false;
		}
		final ApplicationTerm at = ((ApplicationTerm) lhs);
		final Term def = at.getFunction().getDefinition();
		if (def == null) {
			return false;
		}
		final TermVariable[] defVars = at.getFunction().getDefinitionVars();
		final Term[] params = at.getParameters();
		final Term expected = mSkript.let(defVars, params, def);
		return rhs == new FormulaUnLet().unlet(expected);
	}

	boolean checkRewriteSkolem(final Term lhs, final Term rhs, final Term[] skolemFuns) {
		if (!(lhs instanceof QuantifiedFormula)) {
			return false;
		}
		final QuantifiedFormula qf = (QuantifiedFormula) lhs;
		if (qf.getQuantifier() != QuantifiedFormula.EXISTS) {
			return false;
		}

		final TermVariable[] existentialVars = qf.getVariables();
		final Term subformula = qf.getSubformula();
		if (existentialVars.length != skolemFuns.length) {
			return false;
		}
		for (int i = 0; i < existentialVars.length; i++) {
			final Term sk = skolemFuns[i];
			if (!(sk instanceof ApplicationTerm)) {
				return false;
			}
			final ApplicationTerm skApp = (ApplicationTerm) sk;
			if (!compareSkolemDef(skApp, existentialVars[i], qf)) {
				return false;
			}
		}
		final Term expected = mSkript.let(existentialVars, skolemFuns, subformula);
		return rhs == new FormulaUnLet().unlet(expected);
	}

	boolean checkRewriteStoreOverStore(final Term lhs, final Term rhs) {
		// lhs: (store (store a i v) i w)
		// rhs: (store a i w)
		if (!isApplication("store", lhs)) {
			return false;
		}
		final Term[] outerArgs = ((ApplicationTerm) lhs).getParameters();
		if (!isApplication("store", outerArgs[0])) {
			return false;
		}
		final Term[] innerArgs = ((ApplicationTerm) outerArgs[0]).getParameters();
		if (!checkTrivialEquality(innerArgs[1], outerArgs[1])) {
			return false;
		}
		return rhs == mSkript.term("store", innerArgs[0], outerArgs[1], outerArgs[2]);
	}

	boolean checkRewriteSelectOverStore(final Term lhs, final Term rhs) {
		// lhs: (select (store a i v) j) i-j is a constant
		// rhs: (select a j) if i-j !=0. v if i-j = 0
		if (!isApplication("select", lhs)) {
			return false;
		}
		final Term[] selectArgs = ((ApplicationTerm) lhs).getParameters();
		if (!isApplication("store", selectArgs[0])) {
			return false;
		}
		final Term[] storeArgs = ((ApplicationTerm) selectArgs[0]).getParameters();
		if (checkTrivialEquality(storeArgs[1], selectArgs[1])) {
			return rhs == storeArgs[2];
		} else if (checkTrivialDisequality(storeArgs[1], selectArgs[1])) {
			return rhs == mSkript.term("select", storeArgs[0], selectArgs[1]);
		} else {
			return false;
		}
	}

	boolean checkRewriteStore(final Term lhs, final Term rhs) {
		// lhs: (= (store a i v) a) (or symmetric)
		// rhs: (= (select a i) v)
		if (!isApplication("=", lhs)) {
			return false;
		}
		final Term[] eqArgs = ((ApplicationTerm) lhs).getParameters();
		Term[] storeArgs;
		if (isApplication("store", eqArgs[0]) && ((ApplicationTerm) eqArgs[0]).getParameters()[0] == eqArgs[1]) {
			storeArgs = ((ApplicationTerm) eqArgs[0]).getParameters();
		} else if (isApplication("store", eqArgs[1]) && ((ApplicationTerm) eqArgs[1]).getParameters()[0] == eqArgs[0]) {
			storeArgs = ((ApplicationTerm) eqArgs[1]).getParameters();
		} else {
			return false;
		}
		return rhs == mSkript.term("=", mSkript.term("select", storeArgs[0], storeArgs[1]), storeArgs[2]);
	}

	boolean checkRewriteToLeq0(final String rewriteRule, final Term lhs, Term rhs) {
		String func;
		boolean isNegated;
		int firstArg;
		switch (rewriteRule) {
		case ":leqToLeq0":
			func = "<=";
			isNegated = false;
			firstArg = 0;
			break;
		case ":ltToLeq0":
			func = "<";
			isNegated = true;
			firstArg = 1;
			break;
		case ":geqToLeq0":
			func = ">=";
			isNegated = false;
			firstArg = 1;
			break;
		case ":gtToLeq0":
			func = ">";
			isNegated = true;
			firstArg = 0;
			break;
		default:
			return false;
		}
		if (!isApplication(func, lhs)) {
			return false;
		}
		if (isNegated) {
			rhs = negate(rhs);
		}
		if (!isApplication("<=", rhs)) {
			return false;
		}
		final Term[] params = ((ApplicationTerm) lhs).getParameters();
		final SMTAffineTerm expected = new SMTAffineTerm(params[1 - firstArg]);
		expected.negate();
		expected.add(new SMTAffineTerm(params[firstArg]));
		final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
		if (params.length != 2 || rhsParams.length != 2) {
			return false;
		}
		return new SMTAffineTerm(rhsParams[0]).equals(expected) && isZero(rhsParams[1]);
	}

	boolean checkRewriteLeq(final String rewriteRule, final Term lhs, final Term rhs) {
		// (<= c 0) --> true/false if c is constant.
		if (!isApplication("<=", lhs)) {
			return false;
		}
		final Term[] params = ((ApplicationTerm) lhs).getParameters();
		if (params.length != 2 || !isZero(params[1])) {
			return false;
		}
		if (!(params[0] instanceof ConstantTerm)) {
			return false;
		}
		final Rational param0 = SMTAffineTerm.convertConstant((ConstantTerm) params[0]);

		switch (rewriteRule) {
		case ":leqTrue":
			return param0.signum() <= 0 && isApplication("true", rhs);
		case ":leqFalse":
			return param0.signum() > 0 && isApplication("false", rhs);
		default:
			return false;
		}
	}

	boolean checkRewriteIntern(final Term lhs, Term rhs) {
		if (lhs.getSort().getName() != "Bool") {
			return false;
		}

		// x can be rewritten to (= x true) or to (not (= x false))
		if (lhs instanceof TermVariable) {
			boolean isNegRewrite = false;
			if (isApplication("not", rhs)) {
				isNegRewrite = true;
				rhs = negate(rhs);
			}
			rhs = unquote(rhs);
			if (isApplication("=", rhs)) {
				final ApplicationTerm rhsApp = (ApplicationTerm) rhs;
				return isApplication(isNegRewrite ? "false" : "true", rhsApp.getParameters()[1])
						&& lhs == rhsApp.getParameters()[0];
			}
			return false;
		}

		/* Check for auxiliary literals */
		if (isApplication("ite", lhs) || isApplication("or", lhs) || isApplication("xor", lhs)
				|| lhs instanceof MatchTerm) {
			rhs = unquote(rhs, true);
			return lhs == rhs;
		}

		if (!(lhs instanceof ApplicationTerm)) {
			return false;
		}
		final ApplicationTerm at = (ApplicationTerm) lhs;
		if (!at.getFunction().isInterpreted() || at.getFunction().getName() == "select"
				|| at.getFunction().getName() == "is") {
			/* boolean literals are not quoted */
			if (at.getParameters().length == 0) {
				return rhs == at;
			}
			/* second case: boolean functions are created as equalities */
			rhs = unquote(rhs);
			if (!isApplication("=", rhs)) {
				return false;
			}
			final Term[] rhsArgs = ((ApplicationTerm) rhs).getParameters();
			return rhsArgs.length == 2 && rhsArgs[0] == lhs && isApplication("true", rhsArgs[1]);
		}

		if (isApplication("<=", lhs)) {
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			final boolean isInt = lhsParams[0].getSort().getName() == "Int";
			final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParams[0]);
			if (!isZero(lhsParams[1])) {
				return false;
			}

			/* (<= a b) can be translated to (not (< b a)) */
			final boolean isNegated = isApplication("not", rhs);
			boolean isStrict = false;
			if (isNegated) {
				rhs = negate(rhs);
				/* <= (a-b) 0 --> (not (< (b-a) 0)) resp. (not (<= (b-a+1) 0)) for integer */
				lhsAffine.negate();
				if (isInt) {
					lhsAffine.add(Rational.ONE);
				} else {
					isStrict = true;
				}
			}
			// Normalize coefficients
			if (lhs.getFreeVars().length == 0) { // TODO Quantified terms are not normalized, but we might change this.
				lhsAffine.div(lhsAffine.getGcd());
			}
			// Round constant up for integers: (<= (x + 1.25) 0) --> (<= x + 2)
			if (isInt) {
				final Rational constant = lhsAffine.getConstant();
				final Rational frac = constant.add(constant.negate().floor());
				lhsAffine.add(frac.negate());
			}

			// Now check that rhs is as expected
			rhs = unquote(rhs);
			if (!isApplication(isStrict ? "<" : "<=", rhs)) {
				return false;
			}
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			return new SMTAffineTerm(rhsParams[0]).equals(lhsAffine) && isZero(rhsParams[1]);
		}

		if (isApplication("=", lhs)) {
			// TODO Intern rewrites resulting from applying DER on AUX-literals are not really checked here.

			/* compute affine term for lhs */
			final Term[] lhsParams = ((ApplicationTerm) lhs).getParameters();
			if (lhsParams.length != 2) {
				return false;
			}
			if (isApplication("false", rhs)) {
				return checkTrivialDisequality(lhsParams[0], lhsParams[1]);
			} else if (isApplication("true", rhs)) {
				// since we canonicalize SMTAffineTerms, they can only be equal if they are identical.
				return lhsParams[0] == lhsParams[1];
			}

			rhs = unquote(rhs);
			if (!isApplication("=", rhs)) {
				return false;
			}
			final Term[] rhsParams = ((ApplicationTerm) rhs).getParameters();
			if (rhsParams.length != 2) {
				return false;
			}

			/* first check if rhs and lhs are the same or only swapped parameters */
			if (lhs == rhs || (lhsParams[1] == rhsParams[0] && lhsParams[0] == rhsParams[1])) {
				return true;
			}

			// Now it must be an LA equality that got normalized in a different way.
			if (!lhsParams[0].getSort().isNumericSort()) {
				return false;
			}

			/* check that they represent the same equality */
			// Note that an LA equality can sometimes be rewritten to an already existing CC equality, so
			// we cannot assume the rhs is normalized

			final SMTAffineTerm lhsAffine = new SMTAffineTerm(lhsParams[0]);
			lhsAffine.add(Rational.MONE, lhsParams[1]);
			final SMTAffineTerm rhsAffine = new SMTAffineTerm(rhsParams[0]);
			rhsAffine.add(Rational.MONE, rhsParams[1]);
			// we cannot compute gcd on constants so check for this and bail out
			if (lhsAffine.isConstant() || rhsAffine.isConstant()) {
				reportError("A trivial equality was created");
				return false;
			}
			lhsAffine.div(lhsAffine.getGcd());
			rhsAffine.div(rhsAffine.getGcd());
			if (lhsAffine.equals(rhsAffine)) {
				return true;
			}
			rhsAffine.negate();
			return lhsAffine.equals(rhsAffine);
		}
		return false;
	}

	boolean checkRewriteForallExists(final Term lhs, final Term rhs) {
		// lhs: (forall (vs) F)
		// rhs: (not (exists (vs) (not F)))
		if (!isApplication("not", rhs)) {
			return false;
		}
		final Term rhsArg = ((ApplicationTerm) rhs).getParameters()[0];
		if (!(lhs instanceof QuantifiedFormula) || !(rhsArg instanceof QuantifiedFormula)) {
			return false;
		}
		final QuantifiedFormula forall = (QuantifiedFormula) lhs;
		final QuantifiedFormula exists = (QuantifiedFormula) rhsArg;
		if (forall.getQuantifier() != QuantifiedFormula.FORALL || exists.getQuantifier() != QuantifiedFormula.EXISTS) {
			return false;
		}
		if (!Arrays.equals(forall.getVariables(), exists.getVariables())) {
			return false;
		}
		final Term forallSubformula = forall.getSubformula();
		final Term existsSubformula = exists.getSubformula();
		if (!isApplication("not", existsSubformula)) {
			return false;
		}
		return forallSubformula == ((ApplicationTerm) existsSubformula).getParameters()[0];
	}

	boolean checkRewriteRemoveForall(final Term lhs, final Term rhs, final Term[] subst) {
		// lhs is (not (exists ((x1...)) F )).
		// subst is (y1, ..., yn).
		// rhs is (not F [y1/x1]...[yn/xn]).
		if (!isApplication("not", lhs) || !isApplication("not", rhs)) {
			return false;
		}
		final Term exists = ((ApplicationTerm) lhs).getParameters()[0];
		if (!(exists instanceof QuantifiedFormula)) {
			return false;
		}
		final QuantifiedFormula qf = (QuantifiedFormula) exists;
		if (qf.getQuantifier() != QuantifiedFormula.EXISTS) {
			return false;
		}
		// subst must contain as many variables as the lhs has universally quantified variables
		for (final Term s : subst) {
			if (!(s instanceof TermVariable)) {
				return false;
			}
		}
		final TermVariable[] universalVars = qf.getVariables();
		if (universalVars.length != subst.length) {
			return false;
		}
		// check result of substitution
		final Term subformula = qf.getSubformula();
		final Term expected = mSkript.let(universalVars, subst, mSkript.term("not", subformula));
		return rhs == new FormulaUnLet().unlet(expected);
	}

	/**
	 * Convert a clause term into an Array of terms, one entry for each disjunct. This also handles singleton and empty
	 * clause correctly.
	 *
	 * @param clauseTerm
	 *            The term representing a clause.
	 * @return The disjuncts of the clause.
	 */
	private Term[] termToClause(final Term clauseTerm) {
		assert clauseTerm != null && clauseTerm.getSort().getName() == "Bool";
		if (isApplication("or", clauseTerm)) {
			return ((ApplicationTerm) clauseTerm).getParameters();
		} else if (isApplication("false", clauseTerm)) {
			return new Term[0];
		} else {
			/* in all other cases, this is a singleton clause. */
			return new Term[] { clauseTerm };
		}
	}

	/**
	 * Convert a collection of terms into a clause term. This also handles singleton and empty clause correctly.
	 *
	 * @param disjuncts
	 *            the disjuncts of the clause.
	 * @return a term representing the clause.
	 */
	private Term clauseToTerm(final Collection<Term> disjuncts) {
		if (disjuncts.size() <= 1) {
			if (disjuncts.isEmpty()) {
				return mSkript.term("false");
			} else {
				return disjuncts.iterator().next();
			}
		} else {
			final Term[] args = disjuncts.toArray(new Term[disjuncts.size()]);
			return mSkript.term("or", args);
		}
	}

	/**
	 * Handle the resolution rule. The stack should contain the converted input clauses.
	 *
	 * @param resApp
	 *            The <code>{@literal @}res</code> application from the original proof.
	 */
	Term walkResolution(final ApplicationTerm resApp, final Term[] subProofs) {
		/*
		 * allDisjuncts is the currently computed resolution result.
		 */
		final HashSet<Term> allDisjuncts = new HashSet<>();

		/* Now get the disjuncts of the first argument. */
		allDisjuncts.addAll(Arrays.asList(termToClause(subProofs[0])));

		/* Resolve the other clauses */
		for (int i = 1; i < subProofs.length; i++) {
			final AnnotatedTerm pivotPlusProof = (AnnotatedTerm) resApp.getParameters()[i];

			/* Check if it is a pivot-annotation */
			if (pivotPlusProof.getAnnotations().length != 1
					|| pivotPlusProof.getAnnotations()[0].getKey() != ":pivot") {
				reportError("Unexpected Annotation in resolution parameter: " + pivotPlusProof);
				return null;
			}

			final Term pivot = (Term) pivotPlusProof.getAnnotations()[0].getValue();
			/* Remove the negated pivot from allDisjuncts */
			if (!allDisjuncts.remove(negate(pivot))) {
				reportWarning("Could not find negated pivot in main clause");
			}

			/*
			 * For each clause check for the pivot and add all other literals.
			 */
			final Term[] clause = termToClause(subProofs[i]);
			boolean pivotFound = false;
			for (final Term t : clause) {
				if (t == pivot) {
					pivotFound = true;
				} else {
					allDisjuncts.add(t);
				}
			}

			if (!pivotFound) {
				reportWarning("Could not find pivot in secondary clause");
			}
		}

		return clauseToTerm(allDisjuncts);
	}

	/**
	 * Checks that an {@literal @}mp application is okay. The two parameter of the application should already be
	 * converted and their proved formula on the result stack. This puts the resulting formula proved by the
	 * {@literal @}mp application on the result stack.
	 *
	 * @param mpApp
	 *            The {@literal @}mp application.
	 */
	Term walkModusPonens(final ApplicationTerm mpApp, final Term origFormula, final Term rewrite) {
		assert mpApp.getFunction().getName().equals(ProofConstants.FN_MP);

		/*
		 * Expected: The first argument is a boolean formula f the second argument a binary implication (=> f g) or
		 * equality (= f g).
		 *
		 * The second argument is a proof that g is implied by (or equivalent to) f and the result is a proof for g.
		 */
		boolean okay = false;
		Term result = null;
		if (isApplication("=", rewrite) || isApplication("=>", rewrite)) {
			final Term[] mpSides = ((ApplicationTerm) rewrite).getParameters();
			if (mpSides.length == 2) {
				result = mpSides[1];
				okay = (origFormula == mpSides[0]);
			}
		}
		if (!okay && rewrite != null && origFormula != null) {
			reportError("Malformed @eq application: " + origFormula + " and " + rewrite);
		}
		return result;
	}

	Term walkClause(final ApplicationTerm clauseApp, final Term provedClause) {
		/* Check if the parameters of clause are two disjunctions (which they should be) */
		Term expectedClause = clauseApp.getParameters()[1];
		if (expectedClause instanceof AnnotatedTerm) {
			final Annotation[] annot = ((AnnotatedTerm) expectedClause).getAnnotations();
			if (annot.length == 1 && annot[0].getKey().equals(":input")) {
				/* newer version of proof producer adds :input annotation to @clause for interpolator */
				expectedClause = ((AnnotatedTerm) expectedClause).getSubterm();
			}
		}

		// If we had an error, we can silently recover now.
		if (provedClause == null) {
			return expectedClause;
		}

		// The disjuncts of each parameter
		final Term[] provedLits = termToClause(provedClause);
		final Term[] expectedLits = termToClause(expectedClause);
		if (provedLits.length != expectedLits.length) {
			reportError("Clause has different number of literals: " + provedClause + " versus " + expectedClause);
		} else {
			final HashSet<Term> param1Disjuncts = new HashSet<>(Arrays.asList(provedLits));
			final HashSet<Term> param2Disjuncts = new HashSet<>(Arrays.asList(expectedLits));
			/*
			 * Check if the clause operation was correct. Each later disjunct has to be in the first disjunction and
			 * reverse and there should be no double literal.
			 */
			if (!param1Disjuncts.equals(param2Disjuncts) || param1Disjuncts.size() != provedLits.length) {
				reportError("The clause-operation didn't permute correctly!");
			}
		}
		return expectedClause;
	}

	Term walkAllIntro(final ApplicationTerm allApp, final Term origTerm) {
		assert allApp.getFunction().getName() == ProofConstants.FN_ALLINTRO;
		final AnnotatedTerm annotatedTerm = (AnnotatedTerm) allApp.getParameters()[0];
		final Annotation varAnnot = annotatedTerm.getAnnotations()[0];
		if (annotatedTerm.getAnnotations().length != 1 || varAnnot.getKey() != ":vars"
				|| !(varAnnot.getValue() instanceof TermVariable[])) {
			reportError("@allIntro with malformed annotation: " + allApp);
		}
		final TermVariable[] vars = (TermVariable[]) varAnnot.getValue();
		/* compute the resulting quantified term (! (forall (...) origTerm) :quoted) */
		final Theory theory = origTerm.getTheory();
		return theory.annotatedTerm(new Annotation[] { new Annotation(":quoted", null) },
				theory.forall(vars, origTerm));
	}

	/* === Split rules === */

	/**
	 * This function checks whether splitApp is a valid application of a split rule. A split rule proofs a simple clause
	 * that follows from a more complicated asserted formula.
	 *
	 * @param splitApp
	 *            the subproof annotated with the simple clause that is extracted.
	 * @param origTerm
	 *            the term proved by the sub proof.
	 * @return the term proved by the split application, i.e., the simple clause from the annotation.
	 */
	Term walkSplit(final ApplicationTerm splitApp, final Term origTerm) {
		final Annotation splitAnnot = getSingleAnnotation(splitApp.getParameters()[0]);
		final String splitRule = splitAnnot.getKey();
		if (splitRule == null) {
			reportError("Malformed split rule " + splitApp);
			return null;
		}
		final Term splitTerm = splitApp.getParameters()[1];

		// silently recover from previous errors.
		if (origTerm == null) {
			return splitTerm;
		}

		boolean result;
		switch (splitRule) {
		case ":notOr":
			result = checkSplitNotOr(origTerm, splitTerm);
			break;
		case ":xor+1":
		case ":xor+2":
		case ":xor-1":
		case ":xor-2":
			result = checkSplitXor(splitRule, origTerm, splitTerm);
			break;
		case ":ite+1":
		case ":ite+2":
		case ":ite-1":
		case ":ite-2":
			result = checkSplitIte(splitRule, origTerm, splitTerm);
			break;
		case ":subst":
			result = checkSplitSubst((Term[]) splitAnnot.getValue(), origTerm, splitTerm);
			if (splitTerm.getFreeVars().length == 0) {
				// Partial instantiated clauses count when they become ground instances in an inst-lemma.
				mNumInstancesUsed++;
				mNumInstancesFromDER++;
			}
			break;
		default:
			result = false;
		}

		if (!result) {
			reportError("Malformed/unknown split rule " + splitApp);
		}
		return splitTerm;
	}

	boolean checkSplitNotOr(final Term origTerm, final Term splitTerm) {
		// origTerm must be of the form not (or arg0 ... argn),
		// splitTerm is one of the negated arguments.
		// validity follows from (not (or arg0 ... argn)) ==> not argi
		final Term orTerm = negate(origTerm);
		if (!isApplication("or", orTerm)) {
			return false;
		}
		final Term[] lits = ((ApplicationTerm) orTerm).getParameters();
		if (!isApplication("not", splitTerm)) {
			return false;
		}
		final Term disjunct = negate(splitTerm);
		for (final Term t : lits) {
			if (t == disjunct) {
				return true;
			}
		}
		return false;
	}

	boolean checkSplitXor(final String splitRule, Term origTerm, final Term splitTerm) {
		// origTerm is (not? (xor arg0 arg1))
		final boolean positive = !isApplication("not", origTerm);
		if (!positive) {
			origTerm = ((ApplicationTerm) origTerm).getParameters()[0];
		}
		if (!isApplication("xor", origTerm)) {
			return false;
		}
		final Term[] xorParams = ((ApplicationTerm) origTerm).getParameters();
		if (xorParams.length != 2) {
			return false;
		}
		if (!isApplication("or", splitTerm)) {
			return false;
		}
		final Term[] clause = ((ApplicationTerm) splitTerm).getParameters();
		if (clause.length != 2) {
			return false;
		}
		// The validity of the split rules follows from the following implications
		// xor+1: xor arg0 arg1 ==> or arg0 arg1
		// xor+2: xor arg0 arg1 ==> or !arg0 !arg1
		// xor-1: !xor arg0 arg1 ==> or arg0 !arg1
		// xor-2: !xor arg0 arg1 ==> or !arg0 arg1
		switch (splitRule) {
		case ":xor+1":
			return positive && clause[0] == xorParams[0] && clause[1] == xorParams[1];
		case ":xor+2":
			return positive && clause[0] == mSkript.term("not", xorParams[0])
					&& clause[1] == mSkript.term("not", xorParams[1]);
		case ":xor-1":
			return !positive && clause[0] == xorParams[0] && clause[1] == mSkript.term("not", xorParams[1]);
		case ":xor-2":
			return !positive && clause[0] == mSkript.term("not", xorParams[0]) && clause[1] == xorParams[1];
		}
		return false;
	}

	boolean checkSplitIte(final String splitRule, Term origTerm, final Term splitTerm) {
		// origTerm must be of the form (not? (ite c t e))
		final boolean positive = !isApplication("not", origTerm);
		if (!positive) {
			origTerm = ((ApplicationTerm) origTerm).getParameters()[0];
		}
		if (!isApplication("ite", origTerm)) {
			return false;
		}
		final Term[] iteParams = ((ApplicationTerm) origTerm).getParameters();
		if (iteParams.length != 3) {
			return false;
		}
		if (!isApplication("or", splitTerm)) {
			return false;
		}
		final Term[] clause = ((ApplicationTerm) splitTerm).getParameters();
		if (clause.length != 2) {
			return false;
		}
		// The validity of the split rules follows from the following implications
		// ite+1: ite c arg1 arg2 ==> or !c arg1
		// ite+2: ite c arg1 arg1 ==> or c arg2
		// ite-1: !ite c arg1 arg2 ==> or !c !arg1
		// ite-2: !ite c arg1 arg1 ==> or c !arg2
		switch (splitRule) {
		case ":ite+1":
			return positive && clause[0] == mSkript.term("not", iteParams[0]) && clause[1] == iteParams[1];
		case ":ite+2":
			return positive && clause[0] == iteParams[0] && clause[1] == iteParams[2];
		case ":ite-1":
			return !positive && clause[0] == mSkript.term("not", iteParams[0])
					&& clause[1] == mSkript.term("not", iteParams[1]);
		case ":ite-2":
			return !positive && clause[0] == iteParams[0] && clause[1] == mSkript.term("not", iteParams[2]);
		}
		return false;
	}

	boolean checkSplitSubst(final Term[] splitSubst, final Term origTerm, final Term splitTerm) {
		// origTerm must be a quoted universally quantified formula
		final Term unquotedOrigTerm = unquote(origTerm);
		if (!(unquotedOrigTerm instanceof QuantifiedFormula)) {
			return false;
		}
		final QuantifiedFormula qf = (QuantifiedFormula) unquotedOrigTerm;
		if (qf.getQuantifier() != QuantifiedFormula.FORALL) {
			return false;
		}
		final TermVariable[] vars = qf.getVariables();
		if (vars.length != 0 && vars.length == splitSubst.length) {
			final Map<TermVariable, Term> sigma = new HashMap<>();
			for (int i = 0; i < vars.length; i++) {
				// TODO The subst annotation has the variable itself if it is not replaced, it cannot have null values.
				if (splitSubst[i] != null && splitSubst[i] != vars[i]) {
					sigma.put(vars[i], splitSubst[i]);
				}
			}
			final Term[] subst = substituteInQuantClause(qf.getSubformula(), sigma);
			return new HashSet<>(Arrays.asList(subst)).equals(new HashSet<>(Arrays.asList(termToClause(splitTerm))));
		}
		return false;
	}

	/* === Auxiliary functions === */

	void stackPush(final Term pushTerm, final ApplicationTerm keyTerm) {
		mCacheConv.put(keyTerm, pushTerm);
		mStackResults.push(pushTerm);
	}

	Term stackPop() {
		return mStackResults.pop();
	}

	Term unquote(final Term quotedTerm) {
		return unquote(quotedTerm, false);
	}

	Term unquote(final Term quotedTerm, final boolean replaceQuantAux) {
		if (quotedTerm instanceof AnnotatedTerm) {
			final AnnotatedTerm annTerm = (AnnotatedTerm) quotedTerm;
			final Annotation[] annots = annTerm.getAnnotations();
			if (annots.length == 1) {
				final String annot = annots[0].getKey();
				// Check for Quant AUX literals
				if (annot == ":quotedQuant" && annots[0].getValue() instanceof Term) {
					final Term subterm = annTerm.getSubterm();
					if (isApplication("=", subterm)) {
						final ApplicationTerm auxApp = (ApplicationTerm) subterm;
						if (isApplication("true", auxApp.getParameters()[1])) {
							final Term lhs = auxApp.getParameters()[0];
							if (lhs instanceof ApplicationTerm
									&& ((ApplicationTerm) lhs).getFunction().getName().startsWith("@AUX")) {
								// the definition of the quantAuxLit can be found in the annotation
								if (replaceQuantAux) {
									// TODO Check if comparison is needed somewhere else
									if (compareAuxDef(lhs, (Term) annots[0].getValue())) {
										// check that the aux definition matches
										return (Term) annots[0].getValue();
									}
								} else {
									return annTerm.getSubterm();
								}
							}
						}
					}
					reportError("Malformed quantified AUX literal");
				} else if (annot == ":quoted" || annot == ":quotedCC" || annot == ":quotedLA"
						|| annot == ":quotedQuant") {
					final Term result = annTerm.getSubterm();
					return result;
				}
			}
		}
		reportError("Expected quoted literal, but got " + quotedTerm);
		return quotedTerm;
	}

	/**
	 * Negate a term, avoiding double negation. If formula is (not x) it returns x, otherwise it returns (not formula).
	 *
	 * @param formula
	 *            the formula to negate.
	 * @return the negated formula.
	 */
	Term negate(final Term formula) {
		if (isApplication("not", formula)) {
			return ((ApplicationTerm) formula).getParameters()[0];
		}
		return formula.getTheory().term("not", formula);
	}

	/**
	 * Substitute variables in a given quantified clause. This also removes :quotedQuant annotations.
	 *
	 * @param orTerm
	 * @param sigma
	 * @return
	 */
	private Term[] substituteInQuantClause(final Term orTerm, final Map<TermVariable, Term> sigma) {
		final FormulaUnLet unletter = new FormulaUnLet();
		unletter.addSubstitutions(sigma);
		final Term[] lits = termToClause(orTerm);
		final Term[] substLits = new Term[lits.length];
		for (int i = 0; i < lits.length; i++) {
			if (Collections.disjoint(Arrays.asList(lits[i].getFreeVars()), sigma.keySet())) {
				substLits[i] = lits[i];
			} else {
				final boolean isNeg = isApplication("not", lits[i]);
				final Term atom = unquote(isNeg ? negate(lits[i]) : lits[i], false);
				final Term substAtom = unletter.unlet(atom);
				substLits[i] = isNeg ? negate(substAtom) : substAtom;
			}
		}
		return substLits;
	}

	/**
	 * Parses a constant term. It handles Rationals given as ConstantTerm or parsed as div terms.
	 *
	 * @param term
	 *            the term to parse.
	 * @returns the parsed constant, null if parse error occured.
	 */
	Rational parseConstant(Term term) {
		term = SMTAffineTerm.parseConstant(term);
		if (term instanceof ConstantTerm && term.getSort().isNumericSort()) {
			return SMTAffineTerm.convertConstant((ConstantTerm) term);
		}
		return null;
	}

	/**
	 * Checks if a term is an application of an internal function symbol.
	 *
	 * @param funcSym
	 *            the expected function symbol.
	 * @param term
	 *            the term to check.
	 * @return true if term is an application of funcSym.
	 */
	boolean isApplication(final String funcSym, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol func = appTerm.getFunction();
			if (func.isIntern() && func.getName().equals(funcSym)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if a term is an annotation term with a single annotation. Usually the annotation has no value, there are
	 * some exceptions that are checked.
	 *
	 * @param term
	 *            the term to check.
	 * @return the annotation or null if it is not a correct annotation.
	 */
	private Annotation getSingleAnnotation(final Term term) {
		if (term instanceof AnnotatedTerm) {
			final Annotation[] annots = ((AnnotatedTerm) term).getAnnotations();
			if (annots.length == 1) {
				final Annotation singleAnnot = annots[0];
				if (singleAnnot.getKey() == ":subst" || singleAnnot.getKey() == ":skolem"
						|| singleAnnot.getKey() == ":removeForall") {
					if (singleAnnot.getValue() instanceof Term[]) {
						return singleAnnot;
					}
				} else if (singleAnnot.getValue() == null) {
					return singleAnnot;
				}
			}
		}
		return null;
	}

	/**
	 * Check that an {@literal @}AUX term has the same definition as previously seen.
	 */
	private boolean compareAuxDef(final Term auxTerm, final Term defTerm) {
		assert auxTerm instanceof ApplicationTerm
				&& ((ApplicationTerm) auxTerm).getFunction().getName().startsWith("@AUX");
		final ApplicationTerm auxApp = (ApplicationTerm) auxTerm;
		for (final Term p : auxApp.getParameters()) {
			assert p instanceof TermVariable;
		}
		if (!mQuantDefinedTerms.containsKey(auxApp)) {
			mQuantDefinedTerms.put(auxApp, defTerm);
			return true;
		} else {
			return mQuantDefinedTerms.get(auxApp) == defTerm;
		}
	}

	/**
	 * Check that an existentially quantified variable has a unique Skolem function.
	 *
	 * @param skolemApp       the application term {@code (skolem_xyz vars)}. The
	 *                        function symbol should be unique and the parameters
	 *                        should equal the free variables of the existentially
	 *                        quantified formula.
	 * @param var             the variable for which the skolemApp was introduced.
	 * @param quantformula    the existentially quantified formula.
	 * @return true iff this usage of skolemApp matches the previous uses (is only
	 *         used for this quantformula with this variable) and that the arguments
	 *         are the free variables of quantformula.
	 */
	private boolean compareSkolemDef(final ApplicationTerm skolemApp, final TermVariable var, final Term quantformula) {
		// TODO the check is incomplete; we don't check that the func doesn't occur in
		// any input formula.
		final FunctionSymbol func = skolemApp.getFunction();
		if (!Arrays.deepEquals(skolemApp.getParameters(), quantformula.getFreeVars())) {
			return false;
		}
		final Pair<Term, TermVariable> previousUse = mSkolemFunctions.get(func);
		if (previousUse == null) {
			mSkolemFunctions.put(func, new Pair<>(quantformula, var));
			return true;
		} else {
			// TODO: this shouldn't even be reachable, as every rewrite rule is only checked
			// once.
			return previousUse.getFirst() == quantformula && previousUse.getSecond() == var;
		}
	}

	/**
	 * Checks if a term is zero, either Int or Real.
	 *
	 * @param zero
	 *            the term to check.
	 * @return true if zero is 0.
	 */
	boolean isZero(final Term zero) {
		return zero == Rational.ZERO.toTerm(zero.getSort());
	}
}
