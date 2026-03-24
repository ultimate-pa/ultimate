/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.OccurrenceCounter;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ClauseDeletionHook;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.NamedAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.IProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.NoopProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTracker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.resolute.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector.BvToIntUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.ArrayTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCAppTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CClosure;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.DTReverseTrigger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.DataTypeTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LASharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinVar;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantAuxEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant.QuantifierTheory.InstantiationMethod;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TermUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Utility to convert an arbitrary term into CNF and insert it into SMTInterpol.
 *
 * @author Juergen Christ, Jochen Hoenicke
 */
public class Clausifier {

	// flags for all interpreted or boolean terms
	public static final int AUX_AXIOM_ADDED = 16;
	public static final int NEG_AUX_AXIOMS_ADDED = 8;
	public static final int POS_AUX_AXIOMS_ADDED = 4;
	public static final int NEG_AXIOMS_ADDED = 2;
	public static final int POS_AXIOMS_ADDED = 1;

	/// Internalization stuff
	private final FormulaUnLet mUnlet = new FormulaUnLet();
	final TermCompiler mCompiler = new TermCompiler();
	private final OccurrenceCounter mOccCounter = new OccurrenceCounter();
	private final Deque<Operation> mTodoStack = new ArrayDeque<>();

	private final Theory mTheory;
	private final DPLLEngine mEngine;
	private CClosure mCClosure;
	private LinArSolve mLASolver;
	private ArrayTheory mArrayTheory;
	private DataTypeTheory mDataTypeTheory;
	private EprTheory mEprTheory;
	private QuantifierTheory mQuantTheory;

	/**
	 * True, if the run function is already active.
	 */
	private boolean mIsRunning = false;

	// TODO: make map or use option map
	boolean mIsEprEnabled;
	private InstantiationMethod mInstantiationMethod;
	private boolean mIsUnknownTermDawgsEnabled;
	private boolean mPropagateUnknownTerms;
	private boolean mPropagateUnknownAux;

	/**
	 * Mapping from quantified subterms to their aux function application.
	 */
	private final ScopedHashMap<Term, Term> mAnonAuxTerms = new ScopedHashMap<>();
	/**
	 * Mapping from subformulas to their literal, if there was any created.
	 */
	private final ScopedHashMap<Term, ILiteral> mLiterals = new ScopedHashMap<>();
	/**
	 * Mapping from subterms to their CCTerm, if it was created.
	 */
	private final ScopedHashMap<Term, CCTerm> mCCTerms = new ScopedHashMap<>();
	/**
	 * Mapping from subterms to their LASharedTerm if it was created. This is always created for linear affine terms
	 * occuring under an uninterpreted function. It is also created for terms that appear as summand in some linear
	 * affine term.
	 */
	private final ScopedHashMap<Term, LASharedTerm> mLATerms = new ScopedHashMap<>();
	/**
	 * Mapping from subterms/subformulas to information about axioms and other information produced for these terms.
	 */
	private final ScopedHashMap<Term, Integer> mTermDataFlags = new ScopedHashMap<>();

	/**
	 * Keep all shared terms that need to be unshared from congruence closure when the top level is popped off the
	 * assertion stack.
	 */
	final ScopedArrayList<Term> mUnshareCC = new ScopedArrayList<>();
	/**
	 * Map of differences to equality proxies.
	 */
	final ScopedHashMap<Polynomial, EqualityProxy> mEqualities = new ScopedHashMap<>();

	/**
	 * Cache to determine if a sort is stably infinite.
	 */
	private final HashMap<Sort, Boolean> mInfinityMap = new HashMap<>();

	/**
	 * Current assertion stack level.
	 */
	int mStackLevel = 0;
	/**
	 * The number of pushes that failed since the solver already detected unsatisfiability.
	 */
	private int mNumFailedPushes = 0;
	/**
	 * Did we emit a warning on a failed push?
	 */
	private boolean mWarnedInconsistent = false;

	private static int mSkolemCounter = 0;

	private final LogProxy mLogger;
	/**
	 * A tracker for proof production.
	 */
	final IProofTracker mTracker;
	private final LogicSimplifier mUtils;
	private final BvToIntUtils mBvToIntUtils;

	final static ILiteral mTRUE = new TrueLiteral();
	final static ILiteral mFALSE = new FalseLiteral();

	public Clausifier(final Theory theory, final DPLLEngine engine, final ProofMode proofLevel) {
		mTheory = theory;
		mEngine = engine;
		mLogger = engine.getLogger();
		mTracker = proofLevel == ProofMode.NONE || proofLevel == ProofMode.CLAUSES ? new NoopProofTracker()
				: new ProofTracker(theory);
		mUtils = new LogicSimplifier(mTracker);
		mBvToIntUtils = new BvToIntUtils(theory, mTracker, true, mCompiler);
		mCompiler.setProofTracker(mTracker, mUtils, mBvToIntUtils);
	}

	/**
	 * Create a congruence closure term (CCTerm) for the given term. Also creates all necessary axioms for the term or
	 * sub-terms.
	 *
	 * @param term
	 *            The term for which a ccterm should be created.
	 * @param source
	 *            The source annotation that is used for auxiliary axioms.
	 * @return the ccterm.
	 */
	public CCTerm createCCTerm(final Term term, final SourceAnnotation source) {
		final CCTerm ccterm = new CCTermBuilder(this, source).convert(term);
		if (!mIsRunning) {
			run();
		}
		return ccterm;
	}

	/**
	 * Enqueue the build of the given CCTerm. This should only be used in
	 * addTermAxioms or their descendants to trigger the creation of more CCTerms.
	 * These functions are not allowed to recurse into createCCTerm, as they may be
	 * called from inside createCCTerm.
	 *
	 * @param term   The term for which we should build.
	 * @param source The source annotations to map lemmas to their corresponding
	 *               input clause.
	 */
	private void buildCCTerm(final Term term, final SourceAnnotation source) {
		pushOperation(new Operation() {
			@Override
			public void perform() {
				new CCTermBuilder(Clausifier.this, source).convert(term);
			}
		});
	}

	public int getTermFlags(final Term term) {
		final Integer flags = mTermDataFlags.get(term);
		return flags == null ? 0 : (int) flags;
	}

	public void setTermFlags(final Term term, final int newFlags) {
		mTermDataFlags.put(term, newFlags);
	}

	public void share(final CCTerm ccTerm, final LASharedTerm laTerm) {
		getLASolver().addSharedTerm(laTerm);
		getCClosure().addSharedTerm(ccTerm);
	}

	public void shareLATerm(final Term term, final LASharedTerm laTerm) {
		assert !mLATerms.containsKey(term);
		mLATerms.put(term, laTerm);
		final CCTerm ccTerm = getCCTerm(term);
		if (ccTerm != null) {
			share(ccTerm, laTerm);
		}
	}

	public void shareCCTerm(final Term term, final CCTerm ccTerm) {
		assert !mCCTerms.containsKey(term);
		mCCTerms.put(term, ccTerm);
		final LASharedTerm laTerm = getLATerm(term);
		if (laTerm != null) {
			share(ccTerm, laTerm);
		}
	}

	public void addTermAxioms(final Term term, final SourceAnnotation source) {
		final int termFlags = getTermFlags(term);
		if ((termFlags & Clausifier.AUX_AXIOM_ADDED) == 0) {
			setTermFlags(term, termFlags | Clausifier.AUX_AXIOM_ADDED);
			if (term instanceof ApplicationTerm) {
				CCTerm ccTerm = getCCTerm(term);
				if (ccTerm == null && (needCCTerm(term) || term.getSort().isArraySort())) {
					final CCTermBuilder cc = new CCTermBuilder(this, source);
					ccTerm = cc.convert(term);
				}

				final ApplicationTerm at = (ApplicationTerm) term;
				final FunctionSymbol fs = at.getFunction();
				if (fs.isIntern()) {
					/* add axioms for certain built-in functions */
					if (fs.getName().equals("div")) {
						addDivideAxioms(at, source);
					} else if (fs.getName().equals("mod")) {
						addModuloAxioms(at, source);
					} else if (fs.getName().equals("to_int")) {
						addToIntAxioms(at, source);
					} else if (fs.getName().equals("ite") && fs.getReturnSort() != mTheory.getBooleanSort()) {
						pushOperation(new AddTermITEAxiom(this, term, source));
					} else if (fs.getName().equals("store")) {
						addStoreAxiom(at, source);
					} else if (fs.getName().equals(SMTInterpolConstants.DIFF)) {
						addDiffAxiom(at, source);
						mArrayTheory.notifyDiff((CCAppTerm) ccTerm);
					} else if (fs.getName().equals(SMTLIBConstants.UBV_TO_INT)) {
						addBv2NatAxioms(at, ccTerm, source);
					} else if (fs.getName().equals(SMTLIBConstants.INT_TO_BV)) {
						addNat2BvAxiom(at, ccTerm, source);
					}
				}

				if (term.getSort().isBitVecSort()) {
					addBitvectorAxiom(term, ccTerm, source);
				}

				if (term.getSort().isArraySort()) {
					assert ccTerm != null;
					final String funcName = at.getFunction().getName();
					final boolean isStore = funcName.equals("store");
					final boolean isConst = funcName.equals(SMTLIBConstants.CONST);
					mArrayTheory.notifyArray(getCCTerm(term), isStore, isConst);
				}

				if (fs.isConstructor()) {
					final DataType returnSort = (DataType) fs.getReturnSort().getSortSymbol();
					final Constructor c = returnSort.getConstructor(fs.getName());
					mCClosure.addSharedTerm(ccTerm);

					for (final String sel : c.getSelectors()) {
						final FunctionSymbol selFs = mTheory.getFunction(sel, fs.getReturnSort());
						mCClosure.insertReverseTrigger(selFs, ccTerm, 0,
								new DTReverseTrigger(mDataTypeTheory, this, selFs, ccTerm));
					}
					for (final Constructor constr : returnSort.getConstructors()) {
						final String[] index = new String[] { constr.getName() };
						final FunctionSymbol isFs =
								mTheory.getFunctionWithResult("is", index, null, fs.getReturnSort());
						mCClosure.insertReverseTrigger(isFs, ccTerm, 0,
								new DTReverseTrigger(mDataTypeTheory, this, isFs, ccTerm));
					}
				}

			}
			if (term.getSort().isNumericSort()) {
				boolean needsLA = term instanceof ConstantTerm;
				if (term instanceof ApplicationTerm) {
					final String func = ((ApplicationTerm) term).getFunction().getName();
					if (func.equals("+") || func.equals("-") || func.equals("*") || func.equals("to_real")) {
						needsLA = true;
					}
				}
				if (needsLA) {
					final MutableAffineTerm mat = createMutableAffinTerm(new Polynomial(term), source);
					assert mat.getConstant().mEps == 0;
					if (!mLATerms.containsKey(term)) {
						shareLATerm(term, new LASharedTerm(term, mat.getSummands(), mat.getConstant().mReal));
					}
				}
			}
			if (term.getSort() == term.getTheory().getBooleanSort() && !(term instanceof ApplicationTerm
					&& ((ApplicationTerm) term).getFunction().getName().startsWith("@AUX"))) {
				/* If the term is a boolean term, add it's excluded middle axiom */
				if (term != term.getTheory().mTrue && term != term.getTheory().mFalse) {
					addExcludedMiddleAxiom(term, source);
				}
			}
			if (term instanceof MatchTerm) {
				addMatchAxiom((MatchTerm) term, source);
			}
		}
		if (!mIsRunning) {
			run();
		}
	}

	/*
	 * Adds the Axiom that nat2bv(x) equals x mod width Thereby gives an interpretation for nat2bv
	 */
	private void addNat2BvAxiom(final ApplicationTerm at, final CCTerm ccTerm, final SourceAnnotation source) {
		assert at.getFunction().getName() == SMTLIBConstants.INT_TO_BV;
		final Term arg = at.getParameters()[0];
		if (TermUtils.isApplication(SMTLIBConstants.UBV_TO_INT, arg)
				&& ((ApplicationTerm) arg).getParameters()[0].getSort() == at.getSort()) {
			final Term argarg = ((ApplicationTerm) arg).getParameters()[0];
			final Term axiom = mTheory.term("=", at, argarg);
			buildClause(mTracker.tautology(axiom, ProofConstants.TAUT_UBV2INT2BV), source);
		} else {
			// nat2bv(n) = nat2bv(n mod 2^bvlen)
			final int width = Integer.valueOf(at.getSort().getIndices()[0]);
			final Rational modulus = Rational.valueOf(BigInteger.ONE.shiftLeft(width), BigInteger.ONE);
			final Term mod = mBvToIntUtils.normalizeMod(at.getParameters()[0], modulus);
			final Term axiom = mTheory.term("=", at, mTheory.term(at.getFunction(), mod));
			buildClause(mTracker.tautology(axiom, ProofConstants.TAUT_INT2BV), source);
		}
	}

	/*
	 * These method adds Axiom to the Clausifier of the form 0 leq ccTerm leq maxNumber
	 *
	 * At this point, we assume that the parameter of bv2nat can only be an uninterpreted function symbol.
	 */
	private void addBv2NatAxioms(final ApplicationTerm at, final CCTerm ccTerm, final SourceAnnotation source) {
		assert at.getFunction().getName() == SMTLIBConstants.UBV_TO_INT;
		final int width = Integer.valueOf(at.getParameters()[0].getSort().getIndices()[0]);
		// maxNumber = 2 ^ width
		final Rational modulus = Rational.valueOf(BigInteger.ONE.shiftLeft(width), BigInteger.ONE);

		final Term arg = at.getParameters()[0];
		if (TermUtils.isApplication(SMTLIBConstants.INT_TO_BV, arg)) {
			// bv2nat nat2bv n == n mod maxNumber

			final Term mod = mBvToIntUtils.normalizeMod(((ApplicationTerm) arg).getParameters()[0], modulus);
			final Term axiom = mTheory.term("=", at, mod);
			buildClause(mTracker.tautology(axiom, ProofConstants.TAUT_INT2UBV2INT), source);
		} else {
			// 0 <= bv2nat b < maxNumber
			final Sort intSort = mTheory.getSort(SMTLIBConstants.INT);
			final Polynomial leq0LowerBound = new Polynomial();
			leq0LowerBound.add(Rational.MONE, at);
			final Polynomial leq0UpperBound = new Polynomial(at);
			leq0UpperBound.add(modulus.sub(Rational.ONE).negate());
			final Term zero = Rational.ZERO.toTerm(intSort);
			final Term axiomLowerBound2 = mTheory.term("<=", mCompiler.unifyPolynomial(leq0LowerBound, intSort), zero);
			final Term axiomUpperBound2 = mTheory.term("<=", mCompiler.unifyPolynomial(leq0UpperBound, intSort), zero);

			buildClause(mTracker.tautology(axiomLowerBound2, ProofConstants.TAUT_UBV2INTLOW), source);
			buildClause(mTracker.tautology(axiomUpperBound2, ProofConstants.TAUT_UBV2INTHIGH), source);
		}
	}

	/*
	 * These method creates (bv2nat a) and (nat2bv (bv2nat a)) terms for a bitvector
	 * a, so that the corresponding axioms are created.
	 *
	 * But only for bitvectors a that are not nat2bv terms themselves.
	 */
	private void addBitvectorAxiom(final Term term, final CCTerm ccTerm, final SourceAnnotation source) {
		if (TermUtils.isApplication(SMTLIBConstants.INT_TO_BV, term)) {
			final Term arg = ((ApplicationTerm) term).getParameters()[0];
			if (TermUtils.isApplication(SMTLIBConstants.UBV_TO_INT, arg)
					&& ((ApplicationTerm) arg).getParameters()[0].getSort() == term.getSort()) {
				// this is a nat2bv(bv2nat(x)) term with matching sorts.
				// We don't do anything.
				return;
			}

			// this is a nat2bv(y) term but y is not a matching bv2nat. Create the matching
			// bv2nat term.
			buildCCTerm(term.getTheory().term(SMTLIBConstants.UBV_TO_INT, term), source);
		} else {
			// Not a nat2bv bitvector term. Create nat2bv(bv2nat(term)).
			final Term bv2nat = term.getTheory().term(SMTLIBConstants.UBV_TO_INT, term);
			buildCCTerm(term.getTheory().term(SMTLIBConstants.INT_TO_BV, term.getSort().getIndices(), null, bv2nat),
					source);
		}
	}

	/**
	 * Get the (non-basic) linvar for a given term. The term must not be a constant or have arithmetic on the outside.
	 * The term must also be known to the linear solver.
	 *
	 * @param term
	 *            the SMT term.
	 * @return the linvar with linvar.getTerm() == term.
	 */
	public LinVar getLinVar(final Term term) {
		assert term.getSort().isNumericSort();
		assert term == SMTAffineTerm.create(term).getSummands().keySet().iterator().next();
		final LASharedTerm laShared = getLATerm(term);
		assert laShared != null;
		assert laShared.getSummands().size() == 1 && laShared.getOffset() == Rational.ZERO
				&& laShared.getSummands().values().iterator().next() == Rational.ONE;
		return laShared.getSummands().keySet().iterator().next();
	}

	private boolean isMonomial(final Term t) {
		final Polynomial p = new Polynomial(t);
		if (p.getSummands().size() != 1) {
			return false;
		}
		final Map.Entry<Map<Term, Integer>, Rational> entry = p.getSummands().entrySet().iterator().next();
		return !entry.getKey().isEmpty() && entry.getValue() == Rational.ONE;
	}

	/**
	 * Create a LinVar for a basic term. The term must be a non-basic (no arithmetic on the outside and not a constant)
	 * numeric term. This will create a linvar or return an already existing linvar.
	 *
	 * @param term
	 *            a non-basic term
	 * @param source
	 *            the source annotation, which is used to create auxiliary axioms for the term.
	 * @return the linvar with linvar.getTerm() == term.
	 */
	public LinVar createLinVar(final Term term, final SourceAnnotation source) {
		assert term.getSort().isNumericSort();
		assert isMonomial(term);
		if ((term instanceof ApplicationTerm)
				&& ((ApplicationTerm) term).getFunction().getName().equals(SMTLIBConstants.MUL)) {
			for (final Term factor : ((ApplicationTerm) term).getParameters()) {
				addTermAxioms(factor, source);
			}
		} else {
			addTermAxioms(term, source);
		}
		LASharedTerm laShared = getLATerm(term);
		if (laShared == null) {
			final boolean isint = term.getSort().getName().equals("Int");
			final LinVar lv = getLASolver().addVar(term, isint, getStackLevel());
			laShared = new LASharedTerm(term, Collections.singletonMap(lv, Rational.ONE), Rational.ZERO);
			shareLATerm(term, laShared);
		}
		assert laShared.getSummands().size() == 1 && laShared.getOffset() == Rational.ZERO
				&& laShared.getSummands().values().iterator().next() == Rational.ONE;
		return laShared.getSummands().keySet().iterator().next();
	}

	private Term createMonomial(final Map<Term, Integer> monomial) {
		final Polynomial p = new Polynomial();
		p.add(Rational.ONE, monomial);
		final Sort sort = p.isAllIntSummands() ? mTheory.getSort(SMTLIBConstants.INT) : mTheory.getSort(SMTLIBConstants.REAL);
		return mCompiler.unifyPolynomial(p, sort);
	}

	public MutableAffineTerm createMutableAffinTerm(final Polynomial at, final SourceAnnotation source) {
		final MutableAffineTerm res = new MutableAffineTerm();
		for (final Map.Entry<Map<Term, Integer>, Rational> summand : at.getSummands().entrySet()) {
			final Rational coeff = summand.getValue();
			if (summand.getKey().isEmpty()) {
				res.add(coeff);
			} else {
				final Term monomial = createMonomial(summand.getKey());
				final LinVar lv = createLinVar(monomial, source);
				res.add(coeff, lv);
			}
		}
		return res;
	}

	public MutableAffineTerm toMutableAffineTerm(final Polynomial poly) {
		final MutableAffineTerm res = new MutableAffineTerm();
		for (final Map.Entry<Map<Term, Integer>, Rational> summand : poly.getSummands().entrySet()) {
			final Rational coeff = summand.getValue();
			if (summand.getKey().isEmpty()) {
				res.add(coeff);
			} else {
				final Term monomial = createMonomial(summand.getKey());
				final LASharedTerm laShared = getLATerm(monomial);
				if (laShared == null) {
					return null;
				}
				assert laShared.getSummands().size() == 1 && laShared.getOffset() == Rational.ZERO
						&& laShared.getSummands().values().iterator().next() == Rational.ONE;
				res.add(coeff, laShared.getSummands().keySet().iterator().next());
			}
		}
		return res;
	}

	public CCTerm getCCTerm(final Term term) {
		return mCCTerms.get(term);
	}

	public LASharedTerm getLATerm(final Term term) {
		return mLATerms.get(term);
	}

	public ILiteral getILiteral(final Term term) {
		return mLiterals.get(term);
	}

	public void setLiteral(final Term term, final ILiteral lit) {
		mLiterals.put(term, lit);
	}

	public static boolean needCCTerm(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fs = appTerm.getFunction();
			if (fs.isConstructor() || fs.isSelector()) {
				return true;
			}
			if (appTerm.getParameters().length == 0) {
				return false;
			}
			if (!fs.isIntern()) {
				return true;
			}
			if (fs.getName().startsWith("@AUX")) {
				return true;
			}
			if (fs.getName().startsWith("@skolem.")) {
				return true;
			}
			switch (fs.getName()) {
			case "select":
			case "store":
			case SMTInterpolConstants.DIFF:
			case SMTLIBConstants.CONST:
			case "@EQ":
			case "is":
			case SMTLIBConstants.UBV_TO_INT:
			case SMTLIBConstants.INT_TO_BV:
				return true;
			case "div":
			case "mod":
			case "/":
				final Polynomial divisor = new Polynomial(appTerm.getParameters()[1]);
				return !divisor.isConstant() || divisor.isZero();
			default:
				return false;
			}
		}
		return false;
	}

	/**
	 * A QuantifiedFormula is either skolemized or the universal quantifier is dropped before processing the subformula.
	 *
	 * In the existential case, the variables are replaced by Skolem functions over the free variables. In the universal
	 * case, the variables are uniquely renamed.
	 *
	 * @param positive
	 * @param qf
	 * @return a pair of the resulting formula and the variable substitutions.
	 */
	public Pair<Term, Annotation> convertQuantifiedSubformula(final boolean positive, final QuantifiedFormula qf) {
		final TermVariable[] vars = qf.getVariables();
		final Term[] substTerms = new Term[vars.length];
		final Annotation rule;
		if (positive == (qf.getQuantifier() == QuantifiedFormula.EXISTS)) {
			/*
			 * "exists" case (or negative forall case)
			 *
			 * skolemize everything inside, then go on as usual
			 */
			final TermVariable[] freeVars = qf.getFreeVars();
			final Term[] args = new Term[freeVars.length];
			final Sort[] freeVarSorts = new Sort[freeVars.length];
			for (int i = 0; i < freeVars.length; i++) {
				args[i] = freeVars[i];
				freeVarSorts[i] = freeVars[i].getSort();
			}
			final Term[] skolemTerms = new ProofRules(mTheory).getSkolemVars(vars, qf.getSubformula(),
					qf.getQuantifier() == QuantifiedFormula.FORALL);
			for (int i = 0; i < vars.length; ++i) {
				final String skolemName = "@skolem." + vars[i].getName() + "." + mSkolemCounter++;
				final FunctionSymbol fsym = mTheory.declareInternalFunction(skolemName, freeVarSorts, freeVars,
						skolemTerms[i], FunctionSymbol.UNINTERPRETEDINTERNAL);
				substTerms[i] = mTheory.term(fsym, args);
			}

			if (mEprTheory != null) {
				mEprTheory.addSkolemConstants(substTerms);
			}
			rule = qf.getQuantifier() == QuantifiedFormula.EXISTS ? ProofConstants.getTautExistsNeg(substTerms)
					: ProofConstants.getTautForallPos(substTerms);
		} else {
			/*
			 * "forall" case
			 *
			 * treatment of universally quantified subformulas: <li> alpha-rename quantified variables uniquely <li>
			 * drop the quantifier (remaining free TermVariables are implicitly universally quantified)
			 */
			for (int i = 0; i < vars.length; ++i) {
				substTerms[i] = mTheory.createFreshTermVariable(vars[i].getName(), vars[i].getSort());
			}

			rule = qf.getQuantifier() == QuantifiedFormula.EXISTS ? ProofConstants.getTautExistsPos(substTerms)
					: ProofConstants.getTautForallNeg(substTerms);
		}

		final FormulaUnLet unlet = new FormulaUnLet();
		unlet.addSubstitutions(new ArrayMap<>(vars, substTerms));
		Term substituted = unlet.unlet(qf.getSubformula());
		Term pivotLit = qf;
		if (!positive) {
			substituted = mTheory.term("not", substituted);
		} else {
			pivotLit = mTheory.term("not", pivotLit);
		}
		return new Pair<>(substituted, rule);
	}

	public void setAssignmentProduction(final boolean on) {
		mCompiler.setAssignmentProduction(on);
	}

	void pushOperation(final Operation op) {
		mTodoStack.push(op);
	}

	static boolean isNotTerm(final Term t) {
		return (t instanceof ApplicationTerm) && ((ApplicationTerm) t).getFunction().getName() == "not";
	}

	private Term removeDoubleNot(Term t) {
		while (isNotTerm(t) && isNotTerm(((ApplicationTerm) t).getParameters()[0])) {
			t = ((ApplicationTerm) ((ApplicationTerm) t).getParameters()[0]).getParameters()[0];
		}
		return t;
	}

	/**
	 * Transform a term to a positive normal term. A term is a positive normal term if it
	 * <ul>
	 * <li>is an {@link ApplicationTerm} that does not correspond to a negation</li>
	 * <li>is a {@link QuantifiedFormula} that is existentially quantified</li>
	 * </ul>
	 *
	 * @param t
	 *            The term to compute the positive for.
	 * @return The positive of this term.
	 */
	static Term toPositive(final Term t) {
		if (isNotTerm(t)) {
			return ((ApplicationTerm) t).getParameters()[0];
		}
		return t;
	}

	public void buildAuxClause(final ILiteral auxlit, final Term axiom, final SourceAnnotation source) {
		final ApplicationTerm orTerm = (ApplicationTerm) mTracker.getProvedTerm(axiom);
		assert orTerm.getFunction().getName() == "or";
		assert orTerm.getParameters()[0] == auxlit.getSMTFormula(orTerm.getTheory());

		final BuildClause bc = new BuildClause(this, axiom, source);
		/* use the usual engine to create the other literals of the axiom. */
		final Term[] params = orTerm.getParameters();
		pushOperation(bc);
		/* add auxlit directly to prevent it getting converted. No rewrite proof necessary */
		bc.addLiteral(auxlit);
		for (int i = params.length - 1; i >= 1; i--) {
			bc.collectLiteral(params[i]);
		}
	}

	public void buildTautology(final Theory theory, final Term[] clause, final Annotation rule,
			final SourceAnnotation source) {
		final BuildClause bc = new BuildClause(this, mTracker.tautology(theory.term("or", clause), rule), source);
		pushOperation(bc);
		for (final Term term : clause) {
			bc.collectLiteral(term);
		}
	}

	public void buildClause(final Term term, final SourceAnnotation source) {
		final BuildClause bc = new BuildClause(this, term, source);
		pushOperation(bc);
		bc.collectLiteral(mTracker.getProvedTerm(term));
	}

	public void buildClause(final Annotation rule, final SourceAnnotation source, final Term... clauseLits) {
		final Theory t = clauseLits[0].getTheory();
		final Term clauseTerm = clauseLits.length == 1 ? clauseLits[0] : t.term("or", clauseLits);
		final Term tautology = mTracker.tautology(clauseTerm, rule);
		final BuildClause bc = new BuildClause(this, tautology, source);
		pushOperation(bc);
		for (final Term lit : clauseLits) {
			bc.collectLiteral(lit);
		}
	}

	public void buildClauseWithTautology(final Term term, final SourceAnnotation source, final Term[] tautLits,
			final Annotation rule) {
		final Theory t = term.getTheory();
		final Term tautology = mTracker.tautology(t.term("or", tautLits), rule);
		final BuildClause bc = new BuildClause(this, term, source);
		pushOperation(bc);
		bc.addResolution(tautology, mTracker.getProvedTerm(term));
		for (int i = 1; i < tautLits.length; i++) {
			bc.collectLiteral(tautLits[i]);
		}
	}

	/**
	 * Create the auxiliary clauses for Tseitin encoding.
	 *
	 * @param term
	 *            The subformula for which a Tseitin literal was created.
	 * @param positive
	 *            true iff the subformula occurs positive in the clause.
	 * @param source
	 *            The input clause from which this axiom was created.
	 */
	public void addAuxAxioms(final Term term, final boolean positive, final SourceAnnotation source) {
		assert term == toPositive(term);

		final int oldFlags = getTermFlags(term);
		final int auxflag = positive ? Clausifier.POS_AUX_AXIOMS_ADDED : Clausifier.NEG_AUX_AXIOMS_ADDED;
		if ((oldFlags & auxflag) != 0) {
			// We've already added the aux axioms
			// Nothing to do
			return;
		}
		setTermFlags(term, oldFlags | auxflag);

		ILiteral negLit = getILiteral(term);
		assert negLit != null;
		negLit = positive ? negLit.negate() : negLit;
		createDefiningClausesForLiteral(negLit, term, positive, source);
	}

	/**
	 * Create the auxiliary clauses for Tseitin encoding.
	 *
	 * @param term
	 *            The subformula for which a Tseitin literal was created.
	 * @param positive
	 *            true iff the subformula occurs positive in the clause.
	 * @param source
	 *            The input clause from which this axiom was created.
	 */
	public void addAuxAxiomsQuant(final Term term, final Term auxTerm, final SourceAnnotation source) {
		final int oldFlags = getTermFlags(term);
		final int auxflag = Clausifier.POS_AUX_AXIOMS_ADDED | Clausifier.NEG_AUX_AXIOMS_ADDED;
		if ((oldFlags & auxflag) == auxflag) {
			// We've already added the aux axioms
			// Nothing to do
			return;
		}
		setTermFlags(term, oldFlags | auxflag);

		final QuantAuxEquality auxTrueLit = mQuantTheory.createAuxLiteral(auxTerm, term, source);
		final ILiteral auxFalseLit = mQuantTheory.createAuxFalseLiteral(auxTrueLit, source);
		createDefiningClausesForLiteral(auxFalseLit, term, true, source);
		createDefiningClausesForLiteral(auxTrueLit, term, false, source);
	}

	/**
	 * Create the clause that states that the (possibly negated) term implies the literal lit. This clause is used to
	 * define the literal lit, which stands for the subformula term or (not term).
	 *
	 * @param lit
	 *            The literal for the (possibly negated) term. This must be the canonic literal for the (negated) term.
	 * @param term
	 *            The term.
	 * @param negative
	 *            true, iff lit stands for the negated term.
	 * @param source
	 *            The input clause from which this axiom was created.
	 */
	private void createDefiningClausesForLiteral(final ILiteral lit, final Term term, final boolean negative,
			final SourceAnnotation source) {
		final Theory t = term.getTheory();
		final Term litTerm = lit.getSMTFormula(t);
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			Term[] params = at.getParameters();
			if (at.getFunction() == t.mOr) {
				if (negative) {
					// (or (not (or t1 ... tn)) t1 ... tn)
					final Term[] literals = new Term[params.length + 1];
					literals[0] = litTerm;
					System.arraycopy(params, 0, literals, 1, params.length);
					final Term axiom = mTracker.tautology(t.term("or", literals), ProofConstants.TAUT_OR_NEG);
					buildAuxClause(lit, axiom, source);
				} else {
					// (or (or t1 ... tn)) (not ti))
					params = at.getParameters();
					for (final Term p : params) {
						final Term axiom = t.term("or", litTerm, t.term("not", p));
						final Term axiomProof = mTracker.tautology(axiom, ProofConstants.TAUT_OR_POS);
						buildAuxClause(lit, axiomProof, source);
					}
				}
			} else if (at.getFunction() == t.mImplies) {
				if (negative) {
					// (or (not (=> t1 ... tn)) (not t1) ... (not tn-1) tn)
					final Term[] literals = new Term[params.length + 1];
					literals[0] = litTerm;
					for (int i = 0; i < params.length - 1; i++) {
						literals[i + 1] = t.term("not", params[i]);
					}
					literals[params.length] = params[params.length - 1];
					final Term axiom = mTracker.tautology(t.term("or", literals), ProofConstants.TAUT_IMP_NEG);
					buildAuxClause(lit, axiom, source);
				} else {
					// (or (=> t1 ... tn) ti), (or (=> t1 ... tn) (not tn))
					params = at.getParameters();
					for (int i = 0; i < params.length; i++) {
						final Term p = i < params.length - 1 ? params[i] : t.term("not", params[i]);
						final Term axiom = t.term("or", litTerm, p);
						final Term axiomProof = mTracker.tautology(axiom, ProofConstants.TAUT_IMP_POS);
						buildAuxClause(lit, axiomProof, source);
					}
				}
			} else if (at.getFunction() == t.mAnd) {
				if (negative) {
					// (or (not (and t1 ... tn)) ti)
					for (final Term p : params) {
						final Term axiom = t.term("or", litTerm, p);
						final Term axiomProof = mTracker.tautology(axiom, ProofConstants.TAUT_AND_NEG);
						buildAuxClause(lit, axiomProof, source);
					}
				} else {
					// (or (and t1 ... tn) (not t1) ... (not tn))
					final Term[] literals = new Term[params.length + 1];
					literals[0] = litTerm;
					for (int i = 0; i < params.length; i++) {
						literals[i + 1] = t.term("not", params[i]);
					}
					final Term axiom = mTracker.tautology(t.term("or", literals), ProofConstants.TAUT_AND_POS);
					buildAuxClause(lit, axiom, source);
				}
			} else if (at.getFunction().getName().equals("ite")) {
				final Term cond = params[0];
				Term thenTerm = params[1];
				Term elseTerm = params[2];
				if (negative) {
					// (or (not (ite c t e)) (not c) t)
					// (or (not (ite c t e)) c e)
					// (or (not (ite c t e)) t e)
					Term axiom = t.term("or", litTerm, t.term("not", cond), thenTerm);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_ITE_NEG_1);
					buildAuxClause(lit, axiom, source);
					axiom = t.term("or", litTerm, cond, elseTerm);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_ITE_NEG_2);
					buildAuxClause(lit, axiom, source);
					if (Config.REDUNDANT_ITE_CLAUSES) {
						axiom = t.term("or", litTerm, thenTerm, elseTerm);
						axiom = mTracker.tautology(axiom, ProofConstants.TAUT_ITE_NEG_RED);
						buildAuxClause(lit, axiom, source);
					}
				} else {
					// (or (ite c t e) (not c) (not t))
					// (or (ite c t e) c (not e))
					// (or (ite c t e) (not t) (not e))
					thenTerm = t.term("not", thenTerm);
					elseTerm = t.term("not", elseTerm);
					Term axiom = t.term("or", litTerm, t.term("not", cond), thenTerm);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_ITE_POS_1);
					buildAuxClause(lit, axiom, source);
					axiom = t.term("or", litTerm, cond, elseTerm);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_ITE_POS_2);
					buildAuxClause(lit, axiom, source);
					if (Config.REDUNDANT_ITE_CLAUSES) {
						axiom = t.term("or", litTerm, thenTerm, elseTerm);
						axiom = mTracker.tautology(axiom, ProofConstants.TAUT_ITE_POS_RED);
						buildAuxClause(lit, axiom, source);
					}
				}
			} else if (at.getFunction().getName().equals("xor")) {
				assert at.getParameters().length == 2;
				final Term p1 = at.getParameters()[0];
				final Term p2 = at.getParameters()[1];
				// TODO We have the case x=t, and the boolean case as below.
				// Does the case below work for the boolean case with quantifiers?
				assert p1.getSort() == t.getBooleanSort();
				assert p2.getSort() == t.getBooleanSort();
				if (negative) {
					// (or (not (xor p1 p2)) p1 p2)
					// (or (not (xor p1 p2)) (not p1) (not p2))
					Term axiom = t.term("or", litTerm, p1, p2);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_XOR_NEG_1);
					buildAuxClause(lit, axiom, source);
					axiom = t.term("or", litTerm, t.term("not", p1), t.term("not", p2));
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_XOR_NEG_2);
					buildAuxClause(lit, axiom, source);
				} else {
					// (or (xor p1 p2) p1 (not p2))
					// (or (xor p1 p2) (not p1) p2)
					Term axiom = t.term("or", litTerm, p1, t.term("not", p2));
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_XOR_POS_1);
					buildAuxClause(lit, axiom, source);
					axiom = t.term("or", litTerm, t.term("not", p1), p2);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_XOR_POS_2);
					buildAuxClause(lit, axiom, source);
				}
			} else {
				 assert lit instanceof QuantEquality;
				if (negative) {
					// (or (= AUX false) term)
					Term axiom = t.term("or", litTerm, term);
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_EXCLUDED_MIDDLE_2);
					buildAuxClause(lit, axiom, source);
				} else {
					// (or (= AUX true) (not term))
					Term axiom = t.term("or", litTerm, t.term("not", term));
					axiom = mTracker.tautology(axiom, ProofConstants.TAUT_EXCLUDED_MIDDLE_1);
					buildAuxClause(lit, axiom, source);
				}
			}
		} else if (term instanceof MatchTerm) {
			final Theory theory = term.getTheory();
			final MatchTerm mt = (MatchTerm) term;
			final Term dataTerm = mt.getDataTerm();
			final Map<Constructor, Term> cases = new LinkedHashMap<>();
			final Constructor[] constrs = mt.getConstructors();
			for (int caseNr = 0; caseNr < constrs.length; caseNr++) {
				final Constructor c = constrs[caseNr];
				Annotation rule;
				if (cases.containsKey(c)) {
					continue;
				}

				final Deque<Term> clause = new ArrayDeque<>();
				clause.add(litTerm);

				final Map<TermVariable, Term> argSubs = new LinkedHashMap<>();
				if (c == null) {
					// if c == null, this is the default case which matches everything else
					clause.addAll(cases.values());
					argSubs.put(mt.getVariables()[caseNr][0], dataTerm);
					rule = ProofConstants.TAUT_MATCH_DEFAULT;
				} else {
					// build is-condition
					final FunctionSymbol isFs =
							theory.getFunctionWithResult("is", new String[] { c.getName() }, null, dataTerm.getSort());
					final Term isTerm = theory.term(isFs, dataTerm);
					cases.put(c, isTerm);
					clause.add(theory.term("not", isTerm));

					// substitute argument TermVariables with the according selector function
					int s_i = 0;
					for (final String sel : c.getSelectors()) {
						final Term selTerm = theory.term(theory.getFunctionSymbol(sel), dataTerm);
						argSubs.put(mt.getVariables()[caseNr][s_i++], selTerm);
					}
					rule = ProofConstants.TAUT_MATCH_CASE;
				}

				// build implicated literal
				final FormulaUnLet unlet = new FormulaUnLet();
				unlet.addSubstitutions(argSubs);
				final Term equalTerm = unlet.unlet(mt.getCases()[caseNr]);
				if (negative) {
					clause.add(equalTerm);
				} else {
					clause.add(theory.term("not", equalTerm));
				}
				final Term axiom = mTracker.tautology(theory.term("or", clause.toArray(new Term[clause.size()])), rule);
				buildAuxClause(lit, axiom, source);
				if (c == null) {
					// skip all remaining cases
					break;
				}
			}
		} else {
			assert lit instanceof QuantEquality;
			if (negative) {
				// (or (= AUX false) term)
				Term axiom = t.term("or", litTerm, term);
				axiom = mTracker.tautology(axiom, ProofConstants.TAUT_EXCLUDED_MIDDLE_2);
				buildAuxClause(lit, axiom, source);
			} else {
				// (or (= AUX true) (not term))
				Term axiom = t.term("or", litTerm, t.term("not", term));
				axiom = mTracker.tautology(axiom, ProofConstants.TAUT_EXCLUDED_MIDDLE_1);
				buildAuxClause(lit, axiom, source);
			}
		}
	}

	public void addStoreAxiom(final ApplicationTerm store, final SourceAnnotation source) {
		final Theory theory = store.getTheory();
		final Term i = store.getParameters()[1];
		final Term v = store.getParameters()[2];
		final Term axiom = theory.term("=", theory.term("select", store, i), v);

		final Term provedAxiom = mTracker.modusPonens(mTracker.tautology(axiom, ProofConstants.TAUT_ARRAY_STORE),
				mUtils.convertBinaryEq(mTracker.reflexivity(axiom)));
		buildClause(provedAxiom, source);
		if (Config.ARRAY_ALWAYS_ADD_READ
				|| !isStablyInfinite(v.getSort())) {
			final Term a = store.getParameters()[0];
			final Term sel = mTheory.term("select", a, i);
			// Simply create the CCTerm
			buildCCTerm(sel, source);
		}
	}

	public void addDiffAxiom(final ApplicationTerm diff, final SourceAnnotation source) {
		final Theory theory = diff.getTheory();
		// Create a = b \/ select(a, diff(a,b)) != select(b, diff(a,b))
		final Term a = diff.getParameters()[0];
		final Term b = diff.getParameters()[1];
		final Term[] literals = new Term[] { theory.term("=", a, b),
				theory.term("not", theory.term("=", theory.term("select", a, diff), theory.term("select", b, diff))) };
		buildTautology(theory, literals, ProofConstants.TAUT_ARRAY_DIFF, source);
	}

	public void addDivideAxioms(final ApplicationTerm divTerm, final SourceAnnotation source) {
		final Theory theory = divTerm.getTheory();
		final Term[] divParams = divTerm.getParameters();
		final Polynomial divisorPoly = new Polynomial(divParams[1]);
		if (divisorPoly.isZero()) {
			/* Do not add any axiom if divisor is 0. */
			return;
		}
		final Term zero = Rational.ZERO.toTerm(divTerm.getSort());
		final Polynomial diff = new Polynomial(divParams[0]);
		diff.mul(Rational.MONE); // -x
		final Polynomial mulD = new Polynomial(divTerm);
		mulD.mul(divisorPoly); // d * (div x d)
		diff.add(Rational.ONE, mulD); // -x + d * (div x d)

		// (<= (+ (- x) (* d (div x d))) 0)
		final Term axiomLow = theory.term("<=", mCompiler.unifyPolynomial(diff, divTerm.getSort()), zero);
		final Annotation annotLow = new Annotation(ProofConstants.TAUT_DIV_LOW, divTerm);
		if (divisorPoly.isConstant()) {
			buildClause(annotLow, source, axiomLow);
		} else {
			final Term isZero = theory.term(SMTLIBConstants.EQUALS, divParams[1], zero);
			buildClause(annotLow, source, isZero, axiomLow);
		}

		// (not (<= (+ (- x) (* d (div x d) |d|)) 0))
		final Annotation annotHigh = new Annotation(ProofConstants.TAUT_DIV_HIGH, divTerm);
		if (divisorPoly.isConstant()) {
			diff.add(divisorPoly.getConstant().abs());
			final Term axiomHigh = theory.term("not",
					theory.term("<=", mCompiler.unifyPolynomial(diff, divTerm.getSort()), zero));
			buildClause(annotHigh, source, axiomHigh);
		} else {
			final Polynomial divisorPlus1 = new Polynomial(divParams[1]);
			divisorPlus1.add(Rational.ONE);
			final Term notIsNeg = theory.term(SMTLIBConstants.NOT,
					theory.term(SMTLIBConstants.LEQ, mCompiler.unifyPolynomial(divisorPlus1, divTerm.getSort()), zero));
			diff.add(Rational.MONE, divisorPoly);
			final Term axiomHighMinus = theory.term("not",
					theory.term("<=", mCompiler.unifyPolynomial(diff, divTerm.getSort()), zero));
			buildClause(annotHigh, source, notIsNeg, axiomHighMinus);
			final Term notIsPos = theory.term(SMTLIBConstants.LEQ, divParams[1], zero);
			diff.add(Rational.TWO, divisorPoly);
			final Term axiomHighPlus = theory.term("not",
					theory.term("<=", mCompiler.unifyPolynomial(diff, divTerm.getSort()), zero));
			buildClause(annotHigh, source, notIsPos, axiomHighPlus);
		}
	}

	public void addModuloAxioms(final ApplicationTerm modTerm, final SourceAnnotation source) {
		final Theory theory = modTerm.getTheory();
		final Term[] divParams = modTerm.getParameters();
		final Term divTerm = theory.term("div", divParams[0], divParams[1]);
		final Polynomial divisorPoly = new Polynomial(divParams[1]);
		if (divisorPoly.isZero()) {
			/* Do not add any axiom if divisor is 0. */
			return;
		}
		assert !divisorPoly.isConstant();
		final Term zero = Rational.ZERO.toTerm(divTerm.getSort());
		final Term isZero = theory.term(SMTLIBConstants.EQUALS, divParams[1], zero);
		final Polynomial diff = new Polynomial(divParams[0]);
		final Polynomial mulD = new Polynomial(divTerm);
		mulD.mul(divisorPoly); // d * (div x d)
		diff.add(Rational.MONE, mulD); // x - d * (div x d)
		// (or (= d 0) (= (mod x d) (+ (- x) (* d (div x d)))))
		final Term axiom = theory.term("=", modTerm, mCompiler.unifyPolynomial(diff, divTerm.getSort()));
		buildClause(ProofConstants.TAUT_MODULO, source, isZero, axiom);
	}

	/**
	 * Helper to add the auxiliary axioms for to_int axioms. Since the axioms for (to_int x) equal the axioms added for
	 * (div x 1), we reuse AddDivideAxioms.
	 */
	public void addToIntAxioms(final ApplicationTerm toIntTerm, final SourceAnnotation source) {
		final Theory theory = toIntTerm.getTheory();
		final Term realTerm = toIntTerm.getParameters()[0];
		final Term zero = Rational.ZERO.toTerm(realTerm.getSort());
		final Polynomial diff = new Polynomial(realTerm);
		diff.mul(Rational.MONE);
		diff.add(Rational.ONE, toIntTerm);
		// (<= (+ (to_real (to_int x)) (- x)) 0)
		Term axiom = theory.term("<=", mCompiler.unifyPolynomial(diff, realTerm.getSort()), zero);
		buildClause(mTracker.tautology(axiom, new Annotation(ProofConstants.TAUT_TO_INT_LOW, toIntTerm)), source);
		// (not (<= (+ (to_real (to_int x)) (- x) 1) 0))
		diff.add(Rational.ONE);
		axiom = theory.term("not", theory.term("<=", mCompiler.unifyPolynomial(diff, realTerm.getSort()), zero));
		buildClause(mTracker.tautology(axiom, new Annotation(ProofConstants.TAUT_TO_INT_HIGH, toIntTerm)), source);
	}

	/**
	 * Add the axioms for the law of excluded middle. This must happen if a Boolean function is used as a parameter to a
	 * non-Boolean function.
	 */
	public void addExcludedMiddleAxiom(final Term term, final SourceAnnotation source) {
		final Theory theory = term.getTheory();
		final EqualityProxy trueProxy = createEqualityProxy(term, theory.mTrue, source);
		final EqualityProxy falseProxy = createEqualityProxy(term, theory.mFalse, source);
		// These asserts should hold since we do not add excluded middle
		// axioms for true or false, and the equality proxies are
		// non-numeric
		assert trueProxy != EqualityProxy.getTrueProxy();
		assert trueProxy != EqualityProxy.getFalseProxy();
		assert falseProxy != EqualityProxy.getTrueProxy();
		assert falseProxy != EqualityProxy.getFalseProxy();

		final Literal trueLit = trueProxy.getLiteral(source);
		final Literal falseLit = falseProxy.getLiteral(source);

		// term => trueLit is trueLit \/ ~term
		Term axiom = theory.term("or", trueLit.getSMTFormula(theory), theory.term("not", term));
		axiom = mTracker.tautology(axiom, ProofConstants.TAUT_EXCLUDED_MIDDLE_1);
		buildAuxClause(trueLit, axiom, source);

		// ~term => falseLit is falseLit \/ term
		axiom = theory.term("or", falseLit.getSMTFormula(theory), term);
		axiom = mTracker.tautology(axiom, ProofConstants.TAUT_EXCLUDED_MIDDLE_2);
		buildAuxClause(falseLit, axiom, source);
	}

	public void addMatchAxiom(final MatchTerm term, final SourceAnnotation source) {
		final Theory theory = term.getTheory();
		final Term dataTerm = term.getDataTerm();
		final Map<Constructor, Term> cases = new LinkedHashMap<>();
		final Constructor[] constrs = term.getConstructors();
		for (int caseNr = 0; caseNr < constrs.length; caseNr++) {
			final Constructor c = constrs[caseNr];
			if (cases.containsKey(c)) {
				continue;
			}

			final Map<TermVariable, Term> argSubs = new LinkedHashMap<>();
			final Deque<Term> clause = new ArrayDeque<>();
			Annotation rule;
			if (c == null) {
				// if c == null, this is the default case which matches everything else
				clause.addAll(cases.values());
				argSubs.put(term.getVariables()[caseNr][0], dataTerm);
				rule = ProofConstants.TAUT_MATCH_DEFAULT;
			} else {
				// build is-condition
				final FunctionSymbol isFs =
						theory.getFunctionWithResult("is", new String[] { c.getName() }, null, dataTerm.getSort());
				final Term isTerm = theory.term(isFs, dataTerm);
				cases.put(constrs[caseNr], isTerm);
				clause.add(theory.term("not", isTerm));

				// substitute argument TermVariables with the according selector function
				int s_i = 0;
				for (final String sel : c.getSelectors()) {
					final Term selTerm = theory.term(sel, dataTerm);
					argSubs.put(term.getVariables()[caseNr][s_i++], selTerm);
				}
				rule = ProofConstants.TAUT_MATCH_CASE;
			}

			// build implicated equality
			final FormulaUnLet unlet = new FormulaUnLet();
			unlet.addSubstitutions(argSubs);
			final Term caseTerm = mTheory.term("=", term, unlet.unlet(term.getCases()[caseNr]));
			clause.add(caseTerm);
			buildTautology(theory, clause.toArray(new Term[clause.size()]), rule, source);

			if (c == null) {
				// the variable pattern matches everything, so skip the rest.
				break;
			}
		}
	}

	/**
	 * Create an equality proxy for the terms lhs and rhs. This will check for trivial equality and return a false or
	 * true proxy instead. For others it creates the equality proxy. It also creates the terms and their term axioms for
	 * non-trivial equalities.
	 *
	 * @param lhs
	 *            the left-hand side of the equality
	 * @param rhs
	 *            the right-hand side of the equality.
	 * @param source
	 *            the source annotation used for term axioms. Use {@code null} to indicate that terms and their axioms
	 *            have already been created (used for N-O theory combination).
	 * @return the equality proxy.
	 */
	public EqualityProxy createEqualityProxy(final Term lhs, final Term rhs, final SourceAnnotation source) {
		final Polynomial diff = new Polynomial(lhs);
		diff.add(Rational.MONE, rhs);
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				return EqualityProxy.getTrueProxy();
			} else {
				return EqualityProxy.getFalseProxy();
			}
		}
		diff.mul(diff.getGcd().inverse());
		Sort sort = lhs.getSort();
		// normalize equality to integer logic if all variables are integer.
		if (mTheory.getLogic().isIRA() && sort.getName().equals("Real") && diff.isAllIntSummands()) {
			sort = getTheory().getSort("Int");
		}
		// check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
		if (sort.getName().equals("Int") && !diff.getConstant().isIntegral()) {
			return EqualityProxy.getFalseProxy();
		}
		addTermAxioms(lhs, source);
		addTermAxioms(rhs, source);
		// we cannot really normalize the sign of the term. Try both signs.
		EqualityProxy eqForm = mEqualities.get(diff);
		if (eqForm != null) {
			return eqForm;
		}
		diff.mul(Rational.MONE);
		eqForm = mEqualities.get(diff);
		if (eqForm != null) {
			return eqForm;
		}
		eqForm = new EqualityProxy(this, lhs, rhs);
		mEqualities.put(diff, eqForm);
		return eqForm;
	}

	/**
	 * Check if an equality between two terms is trivially true or false.
	 *
	 * @param lhs
	 *            the left side of the equality
	 * @param rhs
	 *            the right side of the equality
	 * @param theory
	 *            the theory
	 * @return the true (false) term if the equality is trivially true (false), null otherwise.
	 */
	public static Term checkAndGetTrivialEquality(final Term lhs, final Term rhs, final Theory theory) {
		// This code corresponds to the check in createEqualityProxy(...)
		final Polynomial diff = new Polynomial(lhs);
		diff.add(Rational.MONE, rhs);
		if (diff.isConstant()) {
			if (diff.getConstant().equals(Rational.ZERO)) {
				return theory.mTrue;
			} else {
				return theory.mFalse;
			}
		} else {
			diff.mul(diff.getGcd().inverse());
			Sort sort = lhs.getSort();
			// Normalize equality to integer logic if all variables are integer.
			if (theory.getLogic().isIRA() && sort.getName().equals("Real") && diff.isAllIntSummands()) {
				sort = theory.getSort("Int");
			}
			// Check for unsatisfiable integer formula, e.g. 2x + 2y = 1.
			if (sort.getName().equals("Int") && !diff.getConstant().isIntegral()) {
				return theory.mFalse;
			}
		}
		return null;
	}

	public Term createQuantAuxTerm(final Term term, final SourceAnnotation source) {
		Term auxTerm = mAnonAuxTerms.get(term);
		if (auxTerm == null) {
			assert mTheory.getLogic().isQuantified() : "quantified variables in quantifier-free theory";
			final TermVariable[] freeVars = new TermVariable[term.getFreeVars().length];
			final Term[] freeVarsAsTerm = new Term[freeVars.length];
			for (int i = 0; i < freeVars.length; i++) {
				freeVars[i] = term.getFreeVars()[i];
				freeVarsAsTerm[i] = freeVars[i];
			}
			final FunctionSymbol fs = mTheory.createFreshAuxFunction(freeVars, term);
			auxTerm = mTheory.term(fs, freeVarsAsTerm);
			addAuxAxiomsQuant(term, auxTerm, source);
			mAnonAuxTerms.put(term, auxTerm);
		}
		return auxTerm;
	}

	public ILiteral createAnonLiteral(final Term term, final SourceAnnotation source) {
		ILiteral lit = getILiteral(term);
		if (lit == null) {
			/*
			 * when inserting a cnf-auxvar (for tseitin-style encoding) in a quantified formula, we need it to depend on
			 * the currently active quantifiers
			 */
			if (term.getFreeVars().length > 0) {
				final Term auxTerm = createQuantAuxTerm(term, source);
				lit = mQuantTheory.createAuxLiteral(auxTerm, term, source);
			} else {
				lit = new NamedAtom(term, mStackLevel);
				mEngine.addAtom((NamedAtom) lit);
			}
			setLiteral(term, lit);
		}
		assert lit != null;
		return lit;
	}

	ILiteral getLiteralTseitin(final Term t, final SourceAnnotation source) {
		final Term idx = toPositive(t);
		final boolean pos = t == idx;
		final ILiteral lit = createAnonLiteral(idx, source);
		// aux axioms will always automatically created for quantified formulas
		if (idx.getFreeVars().length == 0) {
			addAuxAxioms(idx, true, source);
			addAuxAxioms(idx, false, source);
		}
		return pos ? lit : lit.negate();
	}

	void addClause(final Literal[] lits, final ClauseDeletionHook hook, final ProofNode proof) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Added Ground Clause: %s", Arrays.toString(lits));
		}

		// alex, late comment: don't do this here but in BuildClause.perform
		// /*
		// * Idea for EPR:
		// * - a clause that has a literal which has a quantified variable should not go into the Engine
		// * - the EPR theory should know the whole clause
		// * (the engine will set the non-quantified literals, but it "gets to know them" somewhere else (getLiteral or
		// so)
		// */

		// track which constants appear in ground clauses
		if (mEprTheory != null) {
			mEprTheory.addConstants(EprHelpers.collectAppearingConstants(lits, mTheory));
		}

		mEngine.addFormulaClause(lits, proof, hook);
	}

	void addUnshareCC(final Term shared) {
		mUnshareCC.add(shared);
	}

	private void setupCClosure() {
		if (mCClosure == null) {
			mCClosure = new CClosure(this);
			mEngine.addTheory(mCClosure);
			/*
			 * If we do not setup the cclosure at the root level, we remove it with the corresponding pop since the
			 * axiom true != false will be removed from the assertion stack as well.
			 */
			final SourceAnnotation source = SourceAnnotation.EMPTY_SOURCE_ANNOT;
			final Literal atom = createEqualityProxy(mTheory.mTrue, mTheory.mFalse, source).getLiteral(source);
			final Term trueEqFalse = mTheory.term("=", mTheory.mTrue, mTheory.mFalse);
			final Term axiom = mTracker.tautology(mTheory.not(trueEqFalse), ProofConstants.TAUT_TRUE_NOT_FALSE);
			final BuildClause bc = new BuildClause(this, axiom, source);
			bc.mCurrentLits.add(mTheory.not(trueEqFalse));
			final Term rewrite = mTracker.intern(trueEqFalse, atom.getSMTFormula(mTheory));
			bc.addLiteral(atom.negate(), trueEqFalse, rewrite, false);
			bc.perform();
		}
	}

	private void setupLinArithmetic() {
		if (mLASolver == null) {
			mLASolver = new LinArSolve(this);
			mEngine.addTheory(mLASolver);
		}
	}

	private void setupArrayTheory() {
		if (mArrayTheory == null) {
			mArrayTheory = new ArrayTheory(this, mCClosure);
			mEngine.addTheory(mArrayTheory);
		}
	}

	private void setupDataTypeTheory() {
		if (mDataTypeTheory == null) {
			mDataTypeTheory = new DataTypeTheory(this, mTheory, mCClosure);
			mEngine.addTheory(mDataTypeTheory);
		}
	}

	private void setupEprTheory() {
		// TODO maybe merge with setupQuantifiers, below?

		if (mEprTheory == null) {
			// mEprTheory = new EprTheory(this.getTheory());

			mEprTheory = new EprTheory(mTheory, mEngine, mCClosure, this);
			mEngine.addTheory(mEprTheory);
		}
	}

	private void setupQuantifiers() {
		if (mQuantTheory == null) {
			mQuantTheory = new QuantifierTheory(mTheory, mEngine, this, mInstantiationMethod,
					mIsUnknownTermDawgsEnabled, mPropagateUnknownTerms, mPropagateUnknownAux);
			mEngine.addTheory(mQuantTheory);
		}
	}

	public void setQuantifierOptions(final boolean isEprEnabled, final InstantiationMethod instMethod,
			final boolean enableUnknownTermDawgs, final boolean propagateUnknownTerm,
			final boolean propagateUnknownAux) {
		mIsEprEnabled = isEprEnabled;
		mInstantiationMethod = instMethod;
		mIsUnknownTermDawgsEnabled = enableUnknownTermDawgs;
		mPropagateUnknownTerms = propagateUnknownTerm;
		mPropagateUnknownAux = propagateUnknownAux;
	}

	private boolean isBasicStablyInfinite(final Sort sort) {
		assert sort == sort.getRealSort() && !sort.isSortVariable();
		assert !sort.getSortSymbol().isDatatype() && !sort.isArraySort();
		if (sort.equals(sort.getTheory().getBooleanSort()) || sort.isBitVecSort()) {
			// boolean and bitvector sorts are always finite.
			return false;
		} else if (!sort.isInternal()) {
			// uninterpreted sorts are stably infinite unless we have quantifiers.
			return mQuantTheory == null;
		} else {
			// all other internal theories are stably infinite.
			assert sort.isNumericSort();
			return true;
		}
	}

	/**
	 * This function determines if a given sort contains only a single element.
	 *
	 * @param sort the sort in question.
	 * @return True if sort is infinite else False
	 */
	public boolean isSingleton(Sort sort) {
		sort = sort.getRealSort();
		if (sort.isArraySort()) {
			return isSingleton(sort.getArguments()[1]);
		} else if (sort.getSortSymbol().isDatatype()) {
			final Constructor[] cs = ((DataType) sort.getSortSymbol()).getConstructors();
			if (cs.length != 1) {
				return false;
			}
			final Sort[] datatypeParameters = sort.getArguments();
			for (Sort argSort : cs[0].getArgumentSorts()) {
				if (datatypeParameters.length != 0) {
					argSort = argSort.mapSort(datatypeParameters);
				}
				if (!isSingleton(argSort)) {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	/**
	 * This function determines if a given sort is infinite or not.
	 *
	 * @param sort the sort in question.
	 * @return True if sort is infinite else False
	 */
	public boolean isStablyInfinite(Sort sort) {
		sort = sort.getRealSort();
		if (!sort.getSortSymbol().isDatatype() && !sort.isArraySort()) {
			return isBasicStablyInfinite(sort);
		}
		final Boolean cacheVal = mInfinityMap.get(sort);
		if (cacheVal != null) {
			return cacheVal;
		}
		// todo is the stack of sorts, for which we still have to determine the
		// inifinity.
		// dependent is the stack of parent sorts, for which we have not determined
		// infinity yet.
		// if x is in dependent at the beginning of the while loop, it's guaranteed that
		// todo contains x at least once and that all elements after the last occurrence
		// of x are descendents of x.
		final ArrayDeque<Sort> todo = new ArrayDeque<>();
		final Set<Sort> dependent = new LinkedHashSet<>();
		todo.push(sort);
		todo_loop: while (!todo.isEmpty()) {
			final Sort currSort = todo.pop();
			assert currSort.getSortSymbol().isDatatype() || currSort.isArraySort();
			// we may have already determined the status earlier; in that case just take the
			// next todo item.
			if (mInfinityMap.get(currSort) != null) {
				continue todo_loop;
			}
			final Set<Sort> subSorts = new LinkedHashSet<>();
			// Get all dependent subSorts
			if (currSort.getSortSymbol().isDatatype()) {
				final Sort[] datatypeParameters = currSort.getArguments();
				for (final Constructor c : ((DataType) currSort.getSortSymbol()).getConstructors()) {
					for (Sort s : c.getArgumentSorts()) {
						if (datatypeParameters.length > 0) {
							s = s.mapSort(datatypeParameters);
						}
						subSorts.add(s.getRealSort());
					}
				}
			} else {
				final Sort[] indexElemSort = currSort.getArguments();
				// special case for arrays: singleton element sort means
				// array is not stably infinite. In that case we keep the
				// subSorts empty so we go into the false case.
				if (!isSingleton(indexElemSort[1])) {
					subSorts.addAll(Arrays.asList(indexElemSort));
				}
			}
			dependent.add(currSort);
			// check sub sorts, if one of them is stably infinite then currSort is stably infinite.
			// if we find a cycle (currSort appears in dependent), currSort also stably infinite.
			// otherwise we need to check the remaining subSorts first and then try again.
			final Iterator<Sort> iterator = subSorts.iterator();
			while (iterator.hasNext()) {
				final Sort argSort = iterator.next();
				final Boolean isStablyInfinite = dependent.contains(argSort) ? Boolean.TRUE :
						argSort.getSortSymbol().isDatatype() || argSort.isArraySort() ? mInfinityMap.get(argSort)
								: Boolean.valueOf(isBasicStablyInfinite(argSort));
				if (isStablyInfinite != null) {
					iterator.remove();
					if (isStablyInfinite) {
						mInfinityMap.put(currSort, true);
						dependent.remove(currSort);
						continue todo_loop;
					}
				}
			}
			// If we are here, we did not find any stably infinite arg sort.
			// subSorts contains all argument sorts that are still undecided.
			if (!subSorts.isEmpty()) {
				todo.push(currSort);
				for (final Sort s : subSorts) {
					todo.push(s);
				}
			} else {
				// all arg sorts are finite.
				mInfinityMap.put(currSort, false);
				dependent.remove(currSort);
			}
		}
		return mInfinityMap.get(sort);
	}

	public void setLogic(final Logics logic) {
		// Set up the theories.
		// Note that order is important: the easier theories should be first,
		// undecidable theories like quantifier theory should be last.
		if (logic.isUF() || logic.isArray() || logic.isArithmetic() || logic.isQuantified() || logic.isDatatype() || logic.isBitVector()) {
			// also need UF for div/mod
			// and for quantifiers for AUX functions
			setupCClosure();
		}
		if (logic.isArray()) {
			setupArrayTheory();
		}
		if (logic.isDatatype()) {
			setupDataTypeTheory();
		}
		if (logic.isArithmetic() || logic.isBitVector()) {
			setupLinArithmetic();
		}
		if (logic.isQuantified()) {
			// TODO How can we combine the two? For now, we keep EPR separately.
			if (mIsEprEnabled) {
				setupEprTheory();
			} else {
				setupQuantifiers();
			}
		}
	}

	// TODO What do we have to do for quantifiers here?
	public Iterable<BooleanVarAtom> getBooleanVars() {
		final Iterator<ILiteral> it = mLiterals.values().iterator();
		return () -> new Iterator<BooleanVarAtom>() {
			private BooleanVarAtom mNext = computeNext();

			private final BooleanVarAtom computeNext() {
				while (it.hasNext()) {
					final ILiteral lit = it.next();
					if (lit instanceof BooleanVarAtom) {
						return (BooleanVarAtom) lit;
					}
				}
				return null;
			}

			@Override
			public boolean hasNext() {
				return mNext != null;
			}

			@Override
			public BooleanVarAtom next() {
				final BooleanVarAtom res = mNext;
				if (res == null) {
					throw new NoSuchElementException();
				}
				mNext = computeNext();
				return res;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}

	private final void run() {
		try {
			mIsRunning = true;
			while (!mTodoStack.isEmpty()) {
				if (mEngine.isTerminationRequested()) {
					/* Note: Engine remembers incompleteness */
					return;
				}
				final Operation op = mTodoStack.pop();
				op.perform();
			}
		} finally {
			mTodoStack.clear();
			mIsRunning = false;
		}
	}

	public DPLLEngine getEngine() {
		return mEngine;
	}

	public ArrayTheory getArrayTheory() {
		return mArrayTheory;
	}

	public CClosure getCClosure() {
		return mCClosure;
	}

	public LinArSolve getLASolver() {
		return mLASolver;
	}

	public LogProxy getLogger() {
		return mLogger;
	}

	public int getStackLevel() {
		return mStackLevel;
	}

	public void addFormula(final Term f) {
		assert mTodoStack.isEmpty();
		if (mEngine.inconsistent() && !mWarnedInconsistent) {
			mLogger.info("Already inconsistent.");
			mWarnedInconsistent = true;
			return;
		}
		SourceAnnotation source = SourceAnnotation.EMPTY_SOURCE_ANNOT;
		if (mEngine.isProofGenerationEnabled()) {
			if (f instanceof AnnotatedTerm) {
				final AnnotatedTerm at = (AnnotatedTerm) f;
				final Annotation[] annots = at.getAnnotations();
				for (final Annotation a : annots) {
					if (a.getKey().equals(":named")) {
						final String name = ((String) a.getValue()).intern();
						source = new SourceAnnotation(name, null);
						break;
					}
				}
			}
		}
		Term origFormula = mUnlet.unlet(f);
		Term simpFormula;
		try {
			simpFormula = mCompiler.transform(removeDoubleNot(origFormula));
		} finally {
			mCompiler.reset();
		}
		simpFormula = mTracker.modusPonens(mTracker.asserted(origFormula), simpFormula);
		origFormula = null;

		mOccCounter.count(mTracker.getProvedTerm(simpFormula));
		final Map<Term, Set<String>> names = mCompiler.getNames();
		if (names != null) {
			for (final Map.Entry<Term, Set<String>> me : names.entrySet()) {
				trackAssignment(me.getKey(), me.getValue(), source);
			}
		}
		pushOperation(new AddAsAxiom(this, simpFormula, source));
		run();
		mOccCounter.reset(simpFormula);
		simpFormula = null;

		// logger.info("Added " + numClauses + " clauses, " + numAtoms
		// + " auxiliary atoms.");
	}

	public void push() {
		if (mEngine.inconsistent()) {
			if (!mWarnedInconsistent) {
				mLogger.info("Already inconsistent.");
				mWarnedInconsistent = true;
			}
			++mNumFailedPushes;
		} else {
			mEngine.push();
			++mStackLevel;
			mEqualities.beginScope();
			mTermDataFlags.beginScope();
			mLiterals.beginScope();
			mAnonAuxTerms.beginScope();
			mLATerms.beginScope();
			mCCTerms.beginScope();
		}
	}

	public void pop(int numpops) {
		if (numpops <= mNumFailedPushes) {
			mNumFailedPushes -= numpops;
			return;
		}
		mWarnedInconsistent = false;
		numpops -= mNumFailedPushes;
		mNumFailedPushes = 0;
		mEngine.pop(numpops);
		for (int i = 0; i < numpops; ++i) {
			mCCTerms.endScope();
			/* unshare all ccterms that are no longer shared with LA but were in the previous scope */
			for (final Term term : mLATerms.undoMap().keySet()) {
				final CCTerm ccTerm = getCCTerm(term);
				if (ccTerm != null) {
					ccTerm.unshare();
				}
			}
			mLATerms.endScope();
			mLiterals.endScope();
			mAnonAuxTerms.endScope();
			mTermDataFlags.endScope();
			mEqualities.endScope();
		}
		mStackLevel -= numpops;
		mInfinityMap.clear();
	}

	public Theory getTheory() {
		return mTheory;
	}

	/**
	 * This is called for named formulas and creates a literal for the whole term.
	 *
	 * @param term
	 * @param names
	 */
	private void trackAssignment(final Term term, final Set<String> names, final SourceAnnotation source) {
		ILiteral lit;
		final Term idx = toPositive(term);
		final boolean pos = idx == term;
		if (idx instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) idx;
			final FunctionSymbol fs = at.getFunction();
			if (fs.getName().equals("<=")) {
				lit = createLeq0(at, source);
			} else if (fs.getName().equals("=") && at.getParameters()[0].getSort() != mTheory.getBooleanSort()) {
				final EqualityProxy ep = createEqualityProxy(at.getParameters()[0], at.getParameters()[1], source);
				if (ep == EqualityProxy.getTrueProxy()) {
					lit = new DPLLAtom.TrueAtom();
				} else if (ep == EqualityProxy.getFalseProxy()) {
					lit = new DPLLAtom.TrueAtom().negate();
				} else {
					lit = ep.getLiteral(source);
				}
			} else if ((!fs.isIntern() || fs.getName().equals("select"))
					&& fs.getReturnSort() == mTheory.getBooleanSort()) {
				lit = createBooleanLit(at, source);
			} else if (at == mTheory.mTrue) {
				lit = new DPLLAtom.TrueAtom();
			} else if (at == mTheory.mFalse) {
				lit = new DPLLAtom.TrueAtom().negate();
			} else {
				lit = getLiteralTseitin(idx, source);
			}
		} else {
			lit = getLiteralTseitin(idx, source);
		}
		assert lit instanceof Literal;
		if (!pos) {
			lit = lit.negate();
		}
		for (final String name : names) {
			mEngine.trackAssignment(name, (Literal) lit);
		}
	}

	public Literal createLeq0(final ApplicationTerm leq0term, final SourceAnnotation source) {
		Literal lit = (Literal) getILiteral(leq0term);
		if (lit == null) {
			assert ((ConstantTerm) leq0term.getParameters()[1]).getValue() == Rational.ZERO;
			final Polynomial sum = new Polynomial(leq0term.getParameters()[0]);
			final MutableAffineTerm msum = createMutableAffinTerm(sum, source);
			lit = mLASolver.generateConstraint(msum, false);
			setLiteral(leq0term, lit);
			// we don't need to add any aux axioms for (<= t 0) literal.
			setTermFlags(leq0term,
					getTermFlags(leq0term) | Clausifier.POS_AUX_AXIOMS_ADDED | Clausifier.NEG_AUX_AXIOMS_ADDED);
		}
		return lit;
	}

	public ILiteral createBooleanLit(final ApplicationTerm term, final SourceAnnotation source) {
		ILiteral lit = getILiteral(term);
		if (lit == null) {
			if (term.getParameters().length == 0) {
				final DPLLAtom atom = new BooleanVarAtom(term, mStackLevel);
				mEngine.addAtom(atom);
				lit = atom;
			} else {
				if (term.getFreeVars().length > 0 && !mIsEprEnabled) {
					lit = mQuantTheory.getQuantEquality(term, mTheory.mTrue, source);

					// alex: this the right place to get rid of the CClosure predicate conversion in EPR-case?
					// --> seems to be one of three positions.. (keyword: predicate-to-function conversion)
				} else if ((mEprTheory != null && !EprTheorySettings.FullInstatiationMode)
						|| EprTheory.isQuantifiedEprAtom(term)) {
					// assuming right now that
					assert !term.getFunction().getName().equals("not") : "do something for the negated case!";

					// FIXME: how to tell getEprAtom which clause we are in????
					// TODO: replace 0 by hash value
					final EprAtom atom = mEprTheory.getEprAtom(term, 0, mStackLevel, source);
					lit = atom;
					// if (!atom.isQuantified)
					if (atom instanceof EprGroundPredicateAtom) {
						mEprTheory.addAtomToDPLLEngine(atom);
						// mEngine.addAtom(atom);
					}
				} else {
					// replace a predicate atom "(p x)" by "(p x) = true"
					final EqualityProxy eq = createEqualityProxy(term, mTheory.mTrue, source);
					// Safe since m_Term is neither true nor false
					assert eq != EqualityProxy.getTrueProxy();
					assert eq != EqualityProxy.getFalseProxy();
					lit = eq.getLiteral(source);

				}
			}
			setLiteral(term, lit);
			setTermFlags(term, getTermFlags(term) | Clausifier.POS_AUX_AXIOMS_ADDED | Clausifier.NEG_AUX_AXIOMS_ADDED);
		}
		return lit;
	}

	public IProofTracker getTracker() {
		return mTracker;
	}

	public LogicSimplifier getSimplifier() {
		return mUtils;
	}

	// TODO Do we need to change something here for quantifiers?
	// (For now, I added getGroundLit where a method returns a LiteralProxy.)
	public Literal getCreateLiteral(final Term f, final SourceAnnotation source) {
		Term tmp = mUnlet.unlet(f);
		Term tmp2;
		try {
			tmp2 = mCompiler.transform(tmp);
		} finally {
			mCompiler.reset();
		}
		tmp = null;
		mOccCounter.count(tmp2);

		ApplicationTerm at = (ApplicationTerm) mTracker.getProvedTerm(tmp2);
		boolean negated = false;
		FunctionSymbol fs = at.getFunction();
		if (fs == mTheory.mNot) {
			at = (ApplicationTerm) at.getParameters()[0];
			fs = at.getFunction();
			negated = true;
		}

		Literal res;
		if (!fs.isIntern() || fs.getName().equals("select")) {
			final ILiteral iLit = createBooleanLit(at, source);
			assert iLit instanceof Literal;
			res = (Literal) iLit;
		} else if (at == mTheory.mTrue) {
			res = new TrueAtom();
		} else if (at == mTheory.mFalse) {
			res = new TrueAtom().negate();
		} else if (fs.getName().equals("xor")) {
			final ILiteral iLit = getLiteralTseitin(at, source);
			assert iLit instanceof Literal;
			res = (Literal) iLit;
		} else if (fs.getName().equals("=")) {
			final EqualityProxy ep = createEqualityProxy(at.getParameters()[0], at.getParameters()[1], source);
			if (ep == EqualityProxy.getFalseProxy()) {
				res = new TrueAtom().negate();
			} else if (ep == EqualityProxy.getTrueProxy()) {
				res = new TrueAtom();
			} else {
				res = ep.getLiteral(source);
			}
		} else if (fs.getName().equals("<=")) {
			res = createLeq0(at, source);
		} else {
			final ILiteral iLit = getLiteralTseitin(at, source);
			assert iLit instanceof Literal;
			res = (Literal) iLit;
		}

		run();
		mOccCounter.reset(tmp2);
		tmp2 = null;
		return negated ? res.negate() : res;
	}

	public EprTheory getEprTheory() {
		return mEprTheory;
	}

	public QuantifierTheory getQuantifierTheory() {
		return mQuantTheory;
	}

	public TermCompiler getTermCompiler() {
		return mCompiler;
	}

	private static class TrueLiteral implements ILiteral {
		@Override
		public ILiteral getAtom() {
			return this;
		}

		@Override
		public ILiteral negate() {
			return mFALSE;
		}

		@Override
		public boolean isGround() {
			return true;
		}

		@Override
		public Term getSMTFormula(final Theory theory) {
			return theory.mTrue;
		}
	}

	private static class FalseLiteral implements ILiteral {
		@Override
		public ILiteral getAtom() {
			return this;
		}

		@Override
		public ILiteral negate() {
			return mTRUE;
		}

		@Override
		public boolean isGround() {
			return true;
		}

		@Override
		public Term getSMTFormula(final Theory theory) {
			return theory.mFalse;
		}
	}
}
