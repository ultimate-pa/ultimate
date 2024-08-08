/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.io.FileWriter;
import java.io.IOException;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.CheckClosedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbolFactory;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Version;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap.CopyMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SMTInterpolConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.SolverOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.MinimalProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofSimplifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTermGenerator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.PropProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.UnsatCoreCollector;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ErrorCallback.ErrorReason;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ResourceLimit;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.TimeoutHandler;

/**
 * Implementation of the
 * {@link de.uni_freiburg.informatik.ultimate.logic.Script} interface to
 * interact with SMTInterpol.
 *
 * Users should however stick to the
 * {@link de.uni_freiburg.informatik.ultimate.logic.Script} interface which
 * provides most of the methods provided in this class.
 *
 * @author Juergen Christ
 */
public class SMTInterpol extends NoopScript {

	public static enum ProofMode {
		NONE, CLAUSES, FULL, LOWLEVEL
	}

	public static enum CheckType {
		FULL {
			@Override
			boolean check(final DPLLEngine engine) {
				engine.setCompleteness(DPLLEngine.COMPLETE);
				return engine.solve();
			}
		},
		PROPAGATION {
			@Override
			boolean check(final DPLLEngine engine) {
				engine.setCompleteness(DPLLEngine.INCOMPLETE_CHECK);
				return engine.propagate();
			}
		},
		QUICK {
			@Override
			boolean check(final DPLLEngine engine) {
				engine.setCompleteness(DPLLEngine.INCOMPLETE_CHECK);
				return engine.quickCheck();
			}
		};
		abstract boolean check(DPLLEngine engine);
	}

	private static class SMTInterpolSetup extends Theory.SolverSetup {

		public SMTInterpolSetup() {
		}

		@Override
		public void setLogic(final Theory theory, final Logics logic) {
			final Sort[] polySort = theory.createSortVariables("X");
			final Sort bool = theory.getSort("Bool");
			// the EQ function for CC interpolation
			declareInternalPolymorphicFunction(theory, Interpolator.EQ, polySort,
					new Sort[] { polySort[0], polySort[0] }, bool, FunctionSymbol.UNINTERPRETEDINTERNAL);
			defineFunction(theory, new FunctionSymbolFactory("@undefined") {

				@Override
				public int getFlags(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
					return FunctionSymbol.INTERNAL | FunctionSymbol.RETURNOVERLOAD;
				}

				@Override
				public Sort getResultSort(final String[] indices, final Sort[] paramSorts, final Sort resultSort) {
					if (indices != null || paramSorts.length != 0) {
						return null;
					}
					return resultSort;
				}
			});
			if (logic.isArray()) {
				declareArraySymbols(theory);
			}
		}

		private static final void declareArraySymbols(final Theory theory) {
			// Currently only diff
			final Sort[] vars = theory.createSortVariables("Index", "Elem");
			final Sort array = theory.getSort("Array", vars);
			declareInternalPolymorphicFunction(theory, SMTInterpolConstants.DIFF, vars, new Sort[] { array, array },
					vars[0], FunctionSymbol.UNINTERPRETEDINTERNAL);
		}
	}

	private final OptionMap mOptions;
	private final SolverOptions mSolverOptions;
	private BigDecimal mSMTLIBVersion = new BigDecimal("2.0");
	/** The SMTLIB version where string format changed */
	private static final BigDecimal TWO_POINT_FIVE = new BigDecimal("2.5");

	private DPLLEngine mEngine;
	private Clausifier mClausifier;
	private ScopedArrayList<Term> mAssertions;
	private TerminationRequest mCancel;
	private TimeoutHandler mTimeout;
	private ResourceLimit mResourceLimit;

	private final LogProxy mLogger;

	de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model mModel = null;

	private final static Object NAME = new QuotedObject("SMTInterpol", true);
	private final static Object AUTHORS = new QuotedObject(
			"Juergen Christ, Jochen Hoenicke, Alexander Nutz, and Tanja Schindler", true);
	private final static Object INTERPOLATION_METHOD = new QuotedObject("tree", true);
	// I assume an initial check s.t. first (get-info :status) returns sat
	private LBool mStatus = LBool.SAT;

	// The status set in the benchmark
	private LBool mStatusInfo = LBool.UNKNOWN;
	private ReasonUnknown mReasonUnknown = null;

	// The assertion stack was modified after the last check-sat, i.e., the
	// m_status field is not valid and we have to deactivate
	// get-{value,model,interpolants,proof}.
	private boolean mAssertionStackModified = true;

	private long mNextQuickCheck = 1;
	private long mNumAsserts = 0;

	/**
	 * Delta debugger friendly version. Exits with following codes: model-check-mode
	 * fails: 1 interpolant-check-mode fails: 2 exception during check-sat: 3
	 * command that needed sat after last check got unsat: 4 command that needed
	 * unsat after last check got sat: 5
	 */
	private ErrorCallback mErrorCallback = null;

	/**
	 * Default constructor using a default logger and no user termination request.
	 * If this constructor is used, SMTInterpol assumes ownership of the logger.
	 */
	public SMTInterpol() {
		this(new DefaultLogger(), null);
	}

	/**
	 * Construct SMTInterpol with a user-owned logger but without user termination
	 * request.
	 *
	 * @param logger
	 *            The logger owned by the caller.
	 */
	public SMTInterpol(final LogProxy logger) {
		this(logger, null);
	}

	/**
	 * Construct SMTInterpol with a logger but without user termination request. The
	 * logger is assumed to be configured by the user.
	 *
	 * @param logger
	 *            The logger owned by the caller.
	 * @param ignored
	 *            This parameter is ignored!
	 * @deprecated Use a constructor version without the boolean parameter!
	 */
	@Deprecated
	public SMTInterpol(final LogProxy logger, final boolean ignored) {
		this(logger, null);
	}

	/**
	 * Default constructor using a default logger and a given user termination
	 * request.
	 *
	 * @param cancel
	 *            User termination request to poll during checks.
	 */
	public SMTInterpol(final TerminationRequest cancel) {
		this(new DefaultLogger(), cancel);
	}

	/**
	 * Construct SMTInterpol with a logger and a user termination request. This is
	 * the main constructor of SMTInterpol.
	 *
	 * @param logger
	 *            The logger owned by the caller.
	 * @param cancel
	 *            User termination request to poll during checks.
	 */
	public SMTInterpol(final LogProxy logger, final TerminationRequest cancel) {
		this(cancel, new OptionMap(logger));
	}

	/**
	 * Construct SMTInterpol with an option map. SMTInterpol will use the logger
	 * used to initialize the option map.
	 *
	 * @param options
	 *            The option map used to handle all options.
	 */
	public SMTInterpol(final OptionMap options) {
		this(null, options);
	}

	/**
	 * Construct SMTInterpol with a user termination request and a user created
	 * option map. This constructor is mainly used by the front ends to set an
	 * option map including front end options.
	 *
	 * @param cancel
	 *            User termination request to poll during checks.
	 * @param options
	 *            Option map to handle options.
	 */
	public SMTInterpol(final TerminationRequest cancel, final OptionMap options) {
		mLogger = options.getLogProxy();
		mOptions = options;
		mSolverOptions = options.getSolverOptions();
		mCancel = cancel;
		mTimeout = new TimeoutHandler(mCancel);
		mResourceLimit = new ResourceLimit(mTimeout);
		reset();
	}

	/**
	 * Construct SMTInterpol with a user-owned logger but without user termination
	 * request. Note that the logger is assumed to be correctly set up.
	 *
	 * @param logger
	 *            The logger owned by the caller.
	 * @param ignored
	 *            This option is ignored!
	 * @param cancel
	 *            User termination request to poll during checks.
	 * @deprecated Use a constructor version without the boolean parameter.
	 */
	@Deprecated
	public SMTInterpol(final LogProxy logger, final boolean ignored, final TerminationRequest cancel) {
		this(logger, cancel);
	}

	/**
	 * Copy the current context and modify some pre-theory options. The copy shares
	 * the push/pop stack on the symbols but not on the assertions. Users should be
	 * careful not to mess up the push/pop stack, i.e., not to push on one context
	 * and pop on another one.
	 *
	 * Note that this cloning does not clone the assertion stack and should not be
	 * used in multi-threaded contexts since users cannot guarantee correct
	 * push/pop-stack treatment.
	 *
	 * @param other
	 *            The context to clone.
	 * @param options
	 *            The options to set before setting the logic.
	 * @param mode
	 *            What to do when copying existing options.
	 */
	public SMTInterpol(final SMTInterpol other, final Map<String, Object> options, final OptionMap.CopyMode mode) {
		super(other.getTheory());
		mLogger = other.mLogger;
		mOptions = other.mOptions.copy(mode);
		mSolverOptions = mOptions.getSolverOptions();
		if (options != null) {
			for (final Map.Entry<String, Object> me : options.entrySet()) {
				setOption(me.getKey(), me.getValue());
			}
		}
		mCancel = other.mCancel;
		mTimeout = other.mTimeout;
		mResourceLimit = other.mResourceLimit;
		setupClausifier(getTheory().getLogic());
	}

	/**
	 * Set an error callback that will be notified about internal problems in the
	 * solving process: failed model checks, proof checks, interrnal errors, etc.
	 *
	 * @param callback
	 *            The error callback.
	 */
	public void setErrorCallback(final ErrorCallback callback) {
		mErrorCallback = callback;
	}

	// Called in ctor => make it final
	/**
	 * Unset the logic and clear the assertion stack. This does not reset online
	 * modifiable options.
	 */
	@Override
	public final void reset() {
		super.reset();
		mEngine = null;
		mModel = null;
		mAssertionStackModified = true;
		if (mAssertions != null) {
			mAssertions.clear();
		}
		mOptions.reset();
		mNextQuickCheck = 1;
		mNumAsserts = 0;
	}

	@Override
	public final void resetAssertions() {
		super.resetAssertions();
		mAssertionStackModified = true;
		if (mAssertions != null) {
			mAssertions.clear();
		}
		setupClausifier(getTheory().getLogic());
	}

	@Override
	public void push(int n) throws SMTLIBException {
		super.push(n);
		modifyAssertionStack();
		while (n-- > 0) {
			if (mAssertions != null) {
				mAssertions.beginScope();
			}
			mClausifier.push();
		}
	}

	@Override
	public void pop(final int n) throws SMTLIBException {
		try {
			super.pop(n);
		} catch (final SMTLIBException eBug) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.ERROR_ON_POP);
			}
			throw eBug;
		}
		modifyAssertionStack();
		int i = n;
		while (i-- > 0) {
			if (mAssertions != null) {
				mAssertions.endScope();
			}
		}
		mClausifier.pop(n);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		return checkSatAssuming();
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		mModel = null;
		mAssertionStackModified = false;
		mEngine.clearAssumptions();
		if (assumptions != null && assumptions.length != 0) {
			if (Config.STRONG_USAGE_CHECKS) {
				// Check that every literal is a Boolean constant or its negation
				for (final Term ass : assumptions) {
					if (!(ass instanceof ApplicationTerm)) {
						throw new SMTLIBException("Assumption is not a boolean constant");
					}
					final ApplicationTerm at = (ApplicationTerm) ass;
					if (at.getSort() != getTheory().getBooleanSort()) {
						throw new SMTLIBException("Assumption is not a boolean constant");
					}
					if (at.getParameters().length > 1
							|| (at.getParameters().length == 1 && !at.getFunction().getName().equals("not"))) {
						throw new SMTLIBException("Assumption is not a boolean constant");
					}
				}
			}
			// Since checkSatAssuming does not first do bcp and we might have
			// popped, we manually trigger bcp
			if (!mEngine.quickCheck()) {
				return LBool.UNSAT;
			}
			final Literal[] assumptionlits = new Literal[assumptions.length];
			for (int i = 0; i < assumptions.length; ++i) {
				assumptionlits[i] = mClausifier.getCreateLiteral(assumptions[i], new SourceAnnotation("", null));
			}
			mEngine.assume(assumptionlits);
		}
		final long timeout = mSolverOptions.getTimeout();
		if (timeout > 0) {
			mTimeout.setTimeout(timeout);
		}
		final long resouceLimit = mSolverOptions.getReproducibleResourceLimit();
		if (resouceLimit > 0) {
			mResourceLimit.setResourceLimit(resouceLimit);
		}

		LBool result = LBool.UNKNOWN;
		mReasonUnknown = ReasonUnknown.INCOMPLETE;
		mEngine.setRandomSeed(mSolverOptions.getRandomSeed());
		try {
			result = mSolverOptions.getCheckType().check(mEngine) ? LBool.SAT : LBool.UNSAT;
		} catch (final RuntimeException eUnknown) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.EXCEPTION_ON_CHECKSAT);
			}
			throw eUnknown;
		}
		if (result == LBool.SAT) {
			if (mEngine.hasModel()) {
				if (mSolverOptions.isModelCheckModeActive()) {
					try {
						mModel = new de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model(mClausifier,
								getTheory());
						if (!mModel.checkTypeValues(mLogger)) {
							if (mErrorCallback != null) {
								mErrorCallback.notifyError(ErrorReason.INVALID_MODEL);
							}
						}
						for (final Term asserted : mAssertions) {
							final Term checkedResult = mModel.evaluate(asserted);
							if (checkedResult != getTheory().mTrue) {
								mLogger.fatal("Model does not satisfy " + asserted.toStringDirect());
								if (mErrorCallback != null) {
									mErrorCallback.notifyError(ErrorReason.INVALID_MODEL);
								}
								result = LBool.UNKNOWN;
								mReasonUnknown = ReasonUnknown.CRASHED;
							}
						}
					} catch (final UnsupportedOperationException ex) {
						mLogger.warn("Model check mode not working: %s", ex.getMessage());
					} catch (final SMTLIBException ex) {
						mLogger.warn("Model check mode not working: %s", ex.getMessage());
					}
				}
			} else {
				result = LBool.UNKNOWN;
				switch (mEngine.getCompleteness()) {
				case DPLLEngine.COMPLETE:
					if (mSolverOptions.getCheckType() == CheckType.FULL) {
						throw new InternalError("Complete but no model?");
					}
					mReasonUnknown = ReasonUnknown.INCOMPLETE;
					break;
				case DPLLEngine.INCOMPLETE_MEMOUT:
					mReasonUnknown = ReasonUnknown.MEMOUT;
					break;
				case DPLLEngine.INCOMPLETE_TIMEOUT:
					mReasonUnknown = ReasonUnknown.TIMEOUT;
					break;
				case DPLLEngine.INCOMPLETE_QUANTIFIER:
				case DPLLEngine.INCOMPLETE_THEORY:
					mReasonUnknown = ReasonUnknown.INCOMPLETE;
					break;
				case DPLLEngine.INCOMPLETE_UNKNOWN:
					mReasonUnknown = ReasonUnknown.CRASHED;
					break;
				case DPLLEngine.INCOMPLETE_CHECK:
					mReasonUnknown = ReasonUnknown.INCOMPLETE;
					break;
				case DPLLEngine.INCOMPLETE_CANCELLED:
					mReasonUnknown = ReasonUnknown.CANCELLED;
					break;
				default:
					throw new InternalError("Unknown incompleteness reason");
				}
				mLogger.debug("Got %s as reason to return unknown", mEngine.getCompletenessReason());
			}
		} else {
			if (mSolverOptions.isProofCheckModeActive()) {
				final MinimalProofChecker proofchecker = new MinimalProofChecker(this, getLogger());
				if (!proofchecker.check(getProof())) {
					if (mErrorCallback != null) {
						mErrorCallback.notifyError(ErrorReason.INVALID_PROOF);
					}
					mLogger.fatal("Proof-checker did not verify");
					throw new SMTLIBException("Proof-check failed");
				}
			}
		}
		mStatus = result;
		if (Config.CHECK_STATUS_SET && isStatusSet() && result != LBool.UNKNOWN && !result.equals(mStatusInfo)) {
			mLogger.warn("Status differs: User said %s but we got %s", mStatusInfo, result);
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.CHECKSAT_STATUS_DIFFERS);
			}
		}
		mStatusInfo = LBool.UNKNOWN;
		mTimeout.clearTimeout();
		mResourceLimit.clearResourceLimit();
		return result;
	}

	private final boolean isStatusSet() {
		return mStatusInfo != LBool.UNKNOWN;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		try {
			setLogic(Logics.valueOf(logic));
		} catch (final IllegalArgumentException ex) {
			/* Logic is not in enumeration */
			throw new UnsupportedOperationException("Logic " + logic + " not supported");
		}
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mSolverSetup = new SMTInterpolSetup();
		super.setLogic(logic);
		setupClausifier(logic);
	}

	/**
	 * Setup the clausifier and the engine according to the logic, the current proof
	 * production mode, and some other options.
	 *
	 * @param logic
	 *            the SMT-LIB logic to use.
	 * @throws UnsupportedOperationException
	 *             if the logic is not supported by SMTInterpol.
	 */
	private void setupClausifier(final Logics logic) {
		try {
			final ProofMode proofMode = getProofMode();
			mEngine = new DPLLEngine(mLogger, mResourceLimit);
			mClausifier = new Clausifier(getTheory(), mEngine, proofMode);
			// This has to be before set-logic since we need to capture
			// initialization of CClosure.
			mEngine.setProofGeneration(proofMode != ProofMode.NONE);
			mClausifier.setQuantifierOptions(getBooleanOption(SMTInterpolConstants.EPR),
					mSolverOptions.getInstantiationMethod(), getBooleanOption(SMTInterpolConstants.UNKNOWN_TERM_DAWGS),
					getBooleanOption(SMTInterpolConstants.PROPAGATE_UNKNOWN_TERMS),
					getBooleanOption(SMTInterpolConstants.PROPAGATE_UNKNOWN_AUX));
			mClausifier.setLogic(logic);
			final boolean produceAssignments = getBooleanOption(SMTLIBConstants.PRODUCE_ASSIGNMENTS);
			mClausifier.setAssignmentProduction(produceAssignments);
			mEngine.setProduceAssignments(produceAssignments);
			mEngine.setRandomSeed(mSolverOptions.getRandomSeed());
			if (getBooleanOption(SMTLIBConstants.PRODUCE_ASSERTIONS)
					|| (mSolverOptions.isProduceProofs() && mSolverOptions.getProofMode() == ProofMode.LOWLEVEL)
					|| mSolverOptions.isProduceInterpolants() || mSolverOptions.isProofCheckModeActive()
					|| mSolverOptions.isModelCheckModeActive()
					|| getBooleanOption(SMTInterpolConstants.UNSAT_CORE_CHECK_MODE)
					|| getBooleanOption(SMTInterpolConstants.UNSAT_ASSUMPTIONS_CHECK_MODE)) {
				mAssertions = new ScopedArrayList<>();
			}
			mOptions.setOnline();
			getTheory().setGlobalSymbols(getBooleanOption(SMTLIBConstants.GLOBAL_DECLARATIONS));
		} catch (final UnsupportedOperationException eLogicUnsupported) {
			super.reset();
			mEngine = null;
			mClausifier = null;
			throw eLogicUnsupported;
		}
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		final long timeout = mSolverOptions.getTimeout();
		if (timeout > 0) {
			mTimeout.setTimeout(timeout);
		}
		final long resouceLimit = mSolverOptions.getReproducibleResourceLimit();
		if (resouceLimit > 0) {
			mResourceLimit.setResourceLimit(resouceLimit);
		}
		super.assertTerm(term);
		if (!term.getSort().equals(getTheory().getBooleanSort())) {
			if (term.getSort().getTheory() == getTheory()) {
				throw new SMTLIBException("Asserted terms must have sort Bool");
			}
			throw new SMTLIBException("Asserted terms created with incompatible theory");
		}
		if (Config.STRONG_USAGE_CHECKS && !new CheckClosedTerm().isClosed(term)) {
			throw new SMTLIBException("Asserted terms must be closed");
		}
		try {
			modifyAssertionStack();
			if (mEngine.inconsistent()) {
				mLogger.info("Asserting into inconsistent context");
				if (mAssertions != null) {
					mAssertions.add(term);
				}
				return LBool.UNSAT;
			}
			mClausifier.addFormula(term);
			if (mAssertions != null) {
				mAssertions.add(term);
			}
			if (mNumAsserts++ >= mNextQuickCheck) {
				mNextQuickCheck *= 2;
				if (!mEngine.quickCheck()) {
					mLogger.info("Assertion made context inconsistent");
					return LBool.UNSAT;
				}
			}
		} catch (final UnsupportedOperationException ex) {
			throw new SMTLIBException(ex.getMessage());
		} catch (final RuntimeException exc) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.EXCEPTION_ON_ASSERT);
			}
			throw exc;
		} catch (final AssertionError exc) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.EXCEPTION_ON_ASSERT);
			}
			throw exc;
		}
		mTimeout.clearTimeout();
		mResourceLimit.clearResourceLimit();
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (mAssertions != null) {
			return mAssertions.toArray(new Term[mAssertions.size()]);
		}
		throw new SMTLIBException("Set option :interactive-mode to true to get assertions!");
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (!mEngine.isProduceAssignments()) {
			throw new SMTLIBException("Set option :produce-assignments to true to generate assignments!");
		}
		checkAssertionStackModified();
		return mEngine.getAssignments();
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException {
		switch (info) {
		case SMTLIBConstants.STATUS:
			return mStatus;
		case SMTLIBConstants.NAME:
			return NAME;
		case SMTLIBConstants.VERSION:
			return new QuotedObject(Version.VERSION, mSMTLIBVersion.compareTo(TWO_POINT_FIVE) >= 0);
		case SMTLIBConstants.AUTHORS:
			return AUTHORS;
		case SMTLIBConstants.ALL_STATISTICS:
			return mEngine == null ? new Object[0] : mEngine.getStatistics();
		case ":status-set":
			return mStatusInfo;
		case ":options":
			return mOptions.getInfo();
		case SMTLIBConstants.REASON_UNKNOWN:
			if (mStatus != LBool.UNKNOWN) {
				throw new SMTLIBException("Status not unknown");
			}
			return mReasonUnknown;
		case SMTLIBConstants.ASSERTION_STACK_LEVELS:
			return mStackLevel;
		// Info from our SMTLIB interpolation proposal
		case ":interpolation-method":
			return INTERPOLATION_METHOD;
		default:
			return mOptions.getInfo(info, mSMTLIBVersion.compareTo(TWO_POINT_FIVE) >= 0);
		}
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		return mOptions.get(opt);
	}

	/**
	 * Get the proofMode according to the options that are set.
	 *
	 * @returns the proof mode as an enum.
	 */
	private ProofMode getProofMode() {
		return mSolverOptions.getProofMode();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		final ProofMode proofMode = getProofMode();
		if (proofMode == ProofMode.NONE) {
			throw new SMTLIBException("Option :produce-proofs not set to true");
		}
		return getProof(proofMode);
	}

	public Term getProof(final ProofMode proofMode) throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		checkAssertionStackModified();
		final Clause unsat = retrieveProof();
		if (Config.CHECK_PROP_PROOF) {
			final PropProofChecker ppc = new PropProofChecker();
			final boolean correct = ppc.check(unsat);
			assert correct;
		}
		try {
			final ProofTermGenerator generator = new ProofTermGenerator(new ProofRules(getTheory()));
			Term res = generator.convert(unsat);
			if (proofMode == ProofMode.LOWLEVEL) {
				res = new ProofSimplifier(this).transformProof(res);
			}
			return res;
		} catch (final Exception exc) {
			throw new SMTLIBException(exc.getMessage() == null ? exc.toString() : exc.getMessage());
		}
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree) {
		if (getProofMode() == ProofMode.NONE || mAssertions == null) {
			throw new SMTLIBException("Option :produce-interpolants not set to true");
		}
		return getInterpolants(partition, startOfSubtree, getProof(ProofMode.CLAUSES));
	}

	@SuppressWarnings("unchecked")
	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree) {
		final long timeout = mSolverOptions.getTimeout();
		if (timeout > 0) {
			mTimeout.setTimeout(timeout);
		}
		final long resouceLimit = mSolverOptions.getReproducibleResourceLimit();
		if (resouceLimit > 0) {
			mResourceLimit.setResourceLimit(resouceLimit);
		}
		try {
			if (partition.length != startOfSubtree.length) {
				throw new SMTLIBException("Partition table and subtree array need to have equal length");
			}
			if (Config.STRONG_USAGE_CHECKS) {
				for (int i = 0; i < partition.length; i++) {
					if (startOfSubtree[i] < 0) {
						throw new SMTLIBException("subtree array must not contain negative element");
					}
					int j = i;
					while (startOfSubtree[i] < j) {
						j = startOfSubtree[j - 1];
					}
					if (startOfSubtree[i] != j) {
						throw new SMTLIBException("malformed subtree array.");
					}
				}
				if (startOfSubtree[partition.length - 1] != 0) {
					throw new SMTLIBException("malformed subtree array.");
				}
			}
			final Set<String>[] parts = new Set[partition.length];
			final String errormsg = "arguments must be named terms or conjunctions of named terms";
			for (int i = 0; i < partition.length; i++) {
				if (!(partition[i] instanceof ApplicationTerm)) {
					throw new SMTLIBException(errormsg);
				}
				final FunctionSymbol fsym = ((ApplicationTerm) partition[i]).getFunction();
				Term[] terms;
				if (fsym.isIntern()) {
					if (!fsym.getName().equals("and")) {
						throw new SMTLIBException(errormsg);
					}
					terms = ((ApplicationTerm) partition[i]).getParameters();
				} else {
					terms = new Term[] { partition[i] };
				}
				parts[i] = new HashSet<>();
				for (int j = 0; j < terms.length; j++) {
					if (!(terms[j] instanceof ApplicationTerm)) {
						throw new SMTLIBException(errormsg);
					}
					final ApplicationTerm appTerm = (ApplicationTerm) terms[j];
					if (appTerm.getParameters().length != 0) {
						throw new SMTLIBException(errormsg);
					}
					if (appTerm.getFunction().isIntern()) {
						throw new SMTLIBException(errormsg);
					}
					parts[i].add(appTerm.getFunction().getName().intern());
				}
			}
			SMTInterpol checkingSolver = null;
			if (mSolverOptions.isInterpolantCheckModeActive()) {
				final Map<String, Object> newOptions = Collections.singletonMap(SMTLIBConstants.PRODUCE_ASSERTIONS,
						(Object) Boolean.TRUE);
				checkingSolver = new SMTInterpol(this, newOptions, CopyMode.CURRENT_VALUE);
			}
			final Term[] ipls;
			try {
				final Interpolator interpolator = new Interpolator(mLogger, checkingSolver, mAssertions, getTheory(),
						parts, startOfSubtree, mResourceLimit);
				ipls = interpolator.getInterpolants(proofTree);
				if (checkingSolver != null) {
					mLogger.info("FOUND VALID INTERPOLANT");
				}
			} finally {
				if (checkingSolver != null) {
					checkingSolver.exit();
					checkingSolver = null;
				}
			}
			if (mSolverOptions.isSimplifyInterpolants()) {
				final SimplifyDDA simplifier = new SimplifyDDA(
						new SMTInterpol(this,
								Collections.singletonMap(SMTInterpolConstants.CHECK_TYPE,
										(Object) mSolverOptions.getSimplifierCheckType()),
								CopyMode.CURRENT_VALUE),
						getBooleanOption(SMTInterpolConstants.SIMPLIFY_REPEATEDLY));
				for (int i = 0; i < ipls.length; ++i) {
					ipls[i] = simplifier.getSimplifiedTerm(ipls[i]);
				}
			}
			return ipls;
		} catch (final SMTLIBException ex) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.ERROR_ON_GET_INTERPOLANTS);
			}
			throw ex;
		} finally {
			mTimeout.clearTimeout();
			mResourceLimit.clearResourceLimit();
		}
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (!getBooleanOption(SMTLIBConstants.PRODUCE_UNSAT_CORES)) {
			throw new SMTLIBException("Set option :produce-unsat-cores to true before using get-unsat-cores");
		}
		checkAssertionStackModified();
		final Clause unsat = mEngine.getProof();
		if (unsat == null) {
			throw new SMTLIBException("Logical context not inconsistent!");
		}
		final Term[] core = new UnsatCoreCollector(this).getUnsatCore(unsat);
		if (getBooleanOption(SMTInterpolConstants.UNSAT_CORE_CHECK_MODE)) {
			final HashSet<String> usedParts = new HashSet<>();
			for (final Term t : core) {
				usedParts.add(((ApplicationTerm) t).getFunction().getName());
			}
			final SMTInterpol tmpBench = new SMTInterpol(this, null, CopyMode.CURRENT_VALUE);
			final int old = tmpBench.mLogger.getLoglevel();
			try {
				tmpBench.mLogger.setLoglevel(LogProxy.LOGLEVEL_ERROR);
				// Clone the current context except for the parts used in
				// the unsat core
				termloop: for (final Term asserted : mAssertions) {
					if (asserted instanceof AnnotatedTerm) {
						final AnnotatedTerm annot = (AnnotatedTerm) asserted;
						for (final Annotation an : annot.getAnnotations()) {
							if (SMTLIBConstants.NAMED.equals(an.getKey()) && usedParts.contains(an.getValue())) {
								continue termloop;
							}
						}
					}
					tmpBench.assertTerm(asserted);
				}
				for (final Term t : core) {
					tmpBench.assertTerm(t);
				}
				final LBool isUnsat = tmpBench.checkSat();
				if (isUnsat != LBool.UNSAT) {
					mLogger.error("Unsat core could not be proven unsat (Result is %s)", isUnsat);
				}
			} finally {
				tmpBench.mLogger.setLoglevel(old);
				// Not needed for now, but maybe later...
				tmpBench.exit();
			}
		}
		return core;
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		if (!getBooleanOption(SMTLIBConstants.PRODUCE_UNSAT_ASSUMPTIONS)) {
			throw new SMTLIBException(
					"Set option :produce-unsat-assumptions to true before using get-unsat-assumptions");
		}
		checkAssertionStackModified();
		if (!mEngine.inconsistent()) {
			throw new SMTLIBException("Logical context not inconsistent!");
		}
		final Literal[] unsatAssumptionLits = mEngine.getUnsatAssumptions();
		final Term[] unsatAssumptions = new Term[unsatAssumptionLits.length];
		final Theory t = getTheory();
		for (int i = 0; i < unsatAssumptionLits.length; ++i) {
			unsatAssumptions[i] = unsatAssumptionLits[i].negate().getSMTFormula(t);
		}
		if (getBooleanOption(SMTInterpolConstants.UNSAT_ASSUMPTIONS_CHECK_MODE)) {
			final SMTInterpol tmpBench = new SMTInterpol(this, null, CopyMode.CURRENT_VALUE);
			final int old = tmpBench.mLogger.getLoglevel();
			try {
				tmpBench.mLogger.setLoglevel(LogProxy.LOGLEVEL_ERROR);
				// Clone the current context
				for (final Term asserted : mAssertions) {
					tmpBench.assertTerm(asserted);
				}
				for (final Term ass : unsatAssumptions) {
					tmpBench.assertTerm(ass);
				}
				final LBool isUnsat = tmpBench.checkSat();
				if (isUnsat != LBool.UNSAT) {
					mLogger.error("Unsat assumptions could not be proven unsat (Result is %s)", isUnsat);
				}
			} finally {
				tmpBench.mLogger.setLoglevel(old);
				// Not needed for now, but maybe later...
				tmpBench.exit();
			}
		}
		return unsatAssumptions;
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		buildModel();
		return mModel.evaluate(terms);
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null) {
			throw new SMTLIBException("No logic set!");
		}
		buildModel();
		return mModel;
	}

	@Override
	public void setInfo(final String info, final Object value) {
		if (info.equals(SMTLIBConstants.STATUS)) {
			if (value.equals(SMTLIBConstants.SAT)) {
				mStatusInfo = LBool.SAT;
			} else if (value.equals(SMTLIBConstants.UNSAT)) {
				mStatusInfo = LBool.UNSAT;
			} else {
				mStatusInfo = LBool.UNKNOWN;
			}
		}
		if (info.equals(SMTLIBConstants.SMT_LIB_VERSION)) {
			mSMTLIBVersion = (BigDecimal) value;
		}
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		mOptions.set(opt, value);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		final CheckType old = mSolverOptions.getCheckType();
		final int oldNumScopes = mStackLevel;
		try {
			mSolverOptions.setCheckType(mSolverOptions.getSimplifierCheckType());
			return new SimplifyDDA(this, getBooleanOption(SMTInterpolConstants.SIMPLIFY_REPEATEDLY))
					.getSimplifiedTerm(term);
		} finally {
			mSolverOptions.setCheckType(old);
			assert (mStackLevel == oldNumScopes);
		}
	}

	/**
	 * Perform a restart and switch the decisions of all undecided literals. This
	 * method should efficiently lead the solver to explore another path in the
	 * search tree.
	 */
	public void flipDecisions() {
		mEngine.flipDecisions();
	}

	/**
	 * Flip the truth value decision for a name literal.
	 *
	 * @param name
	 *            The name used in the annotation for this literal.
	 * @throws SMTLIBException
	 *             If name not known.
	 */
	public void flipNamedLiteral(final String name) throws SMTLIBException {
		mEngine.flipNamedLiteral(name);
	}

	/**
	 * Access to the internal CNF transformer. Should not be used by users.
	 *
	 * @return Internal CNF transformer.
	 */
	public Clausifier getClausifier() {
		return mClausifier;
	}

	/**
	 * Access to the internal DPLL engine. Should not be used by users.
	 *
	 * @return Internal DPLL engine.
	 */
	public DPLLEngine getEngine() {
		return mEngine;
	}

	/**
	 * Access to the logger used by SMTInterpol.
	 *
	 * @return The logger used by SMTInterpol.
	 */
	public LogProxy getLogger() {
		return mLogger;
	}

	protected void setEngine(final DPLLEngine engine) {
		mEngine = engine;
	}

	protected void setClausifier(final Clausifier clausifier) {
		mClausifier = clausifier;
	}

	private void checkAssertionStackModified() throws SMTLIBException {
		if (mAssertionStackModified) {
			throw new SMTLIBException("Assertion stack has been modified since last check-sat!");
		}
	}

	private void modifyAssertionStack() {
		mAssertionStackModified = true;
		mModel = null;
		mEngine.clearAssumptions();
	}

	private void buildModel() throws SMTLIBException {
		checkAssertionStackModified();
		if (mEngine.inconsistent()) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.GET_MODEL_BUT_UNSAT);
			}
			throw new SMTLIBException("Context is inconsistent");
		}
		if (mStatus != LBool.SAT) {
			// Once we have incomplete solvers we might check mReasonUnknown...
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.GET_MODEL_BUT_UNKNOWN);
			}
			throw new SMTLIBException("Cannot construct model since solving did not complete");
		}
		if (mModel == null) {
			mModel = new de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model(mClausifier, getTheory());
		}
	}

	/**
	 * Retrieve the proof in its internal format. Users should use
	 * {@link #getProof()} to retrieve the proof as a proof term.
	 *
	 * @return Internal proof.
	 * @throws SMTLIBException
	 *             If no proof is present or the proof is found to to be incorrect.
	 */
	@SuppressWarnings("unused")
	public Clause retrieveProof() throws SMTLIBException {
		final Clause unsat = mEngine.getProof();
		if (unsat == null) {
			if (mErrorCallback != null) {
				mErrorCallback.notifyError(ErrorReason.GET_PROOF_BUT_SAT);
			}
			throw new SMTLIBException("Logical context not inconsistent!");
		}
		final Clause proof = mSolverOptions.getProofTransformation().transform(unsat);
		if (Config.CHECK_PROP_PROOF && (proof.getSize() != 0 || !new PropProofChecker().check(proof))) {
			throw new SMTLIBException("Proof incorrect");
		}
		return proof;
	}

	/**
	 * Get all literals currently set to true. Note that this function might also be
	 * called if SMTInterpol is currently in an unsat state. Then, it will simply
	 * return an empty array.
	 *
	 * @return All literals currently set to true.
	 * @throws SMTLIBException
	 *             If the assertion stack is modified since the last clean state.
	 */
	public Term[] getSatisfiedLiterals() throws SMTLIBException {
		checkAssertionStackModified();
		return mEngine.getSatisfiedLiterals(getTheory());
	}

	/**
	 * A helper function to be called from the debugger...
	 */
	@SuppressWarnings("unused")
	private boolean dumpInterpolationBug(final int[] startOfSubtree, final Term[] partition, final Term[] ipls,
			final int num) {
		try {
			final FileWriter fw = new FileWriter("iplBug.txt");
			final FormulaUnLet unlet = new FormulaUnLet();
			final PrintTerm outputter = new PrintTerm();
			// Find and assert children
			int child = num - 1;
			while (child >= startOfSubtree[num]) {
				outputter.append(fw, unlet.unlet(ipls[child]));
				child = startOfSubtree[child] - 1;
				fw.append("\nand\n");
			}
			// Assert node
			outputter.append(fw, ((ApplicationTerm) partition[num]).getFunction().getDefinition());
			fw.append('\n');
			// Assert negated interpolant
			if (num != ipls.length) {
				fw.append("==>\n");
				outputter.append(fw, unlet.unlet(ipls[num]));
				fw.append('\n');
			}
			fw.flush();
			fw.close();
			return true;
		} catch (final IOException eioe) {
			eioe.printStackTrace();
			return false;
		}
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] input) {
		final Literal[] lits = new Literal[input.length];
		for (int i = 0; i < input.length; ++i) {
			if (input[i].getSort() != getTheory().getBooleanSort()) {
				throw new SMTLIBException("AllSAT over non-Boolean");
			}
			lits[i] = mClausifier.getCreateLiteral(input[i], new SourceAnnotation("", null));
		}
		return new Iterable<Term[]>() {

			@Override
			public Iterator<Term[]> iterator() {
				return mEngine.new AllSatIterator(lits, input);
			}
		};
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y)
			throws SMTLIBException, UnsupportedOperationException {
		if (x.length != y.length) {
			throw new SMTLIBException("Different number of x's and y's");
		}
		if (x.length < 2) {
			throw new SMTLIBException("Need at least two elements to find equality");
		}
		for (int i = 0; i < x.length; ++i) {
			if (!x[i].getSort().isNumericSort() || !y[i].getSort().isNumericSort()) {
				throw new SMTLIBException("Only numeric types supported");
			}
		}
		final LBool isSat = checkSat();
		if (isSat == LBool.UNSAT) {
			throw new SMTLIBException("Context is inconsistent!");
		}
		// TODO: If we get unknown, we can nevertheless try. But quick-check
		// on numerals won't work since it produces a really dull model
		// since it does not allow pivoting
		// if (isSat == LBool.UNKNOWN)
		// // We cannot even prove satisfiability of the context. No chance to
		// // prove inductivity of an equality!
		// return new Term[0];
		final Term[] terms = new Term[x.length + y.length];
		System.arraycopy(x, 0, terms, 0, x.length);
		System.arraycopy(y, 0, terms, x.length, y.length);
		final Map<Term, Term> vals = getValue(terms);
		final Rational x0 = (Rational) ((ConstantTerm) vals.get(x[0])).getValue();
		final Rational y0 = (Rational) ((ConstantTerm) vals.get(y[0])).getValue();
		Rational x1 = null, y1 = null;
		for (int i = 1; i < x.length; ++i) {
			x1 = (Rational) ((ConstantTerm) vals.get(x[i])).getValue();
			y1 = (Rational) ((ConstantTerm) vals.get(y[i])).getValue();
			if (x1.equals(x0)) {
				if (!y1.equals(y0)) {
					// There is no implied equality!
					return new Term[0];
				}
			} else {
				break;
			}
		}
		final Rational xdiff = x0.sub(x1);
		if (xdiff.equals(Rational.ZERO)) {
			// There is no implied equality
			return new Term[0];
		}
		Rational a = y0.subdiv(y1, xdiff);
		Rational b = Rational.ONE;
		Rational c = y0.mul(x1).subdiv(x0.mul(y1), xdiff);
		Sort s = x[0].getSort();
		// Check for integers
		if (x[0].getSort().getName().equals("Int") && y[0].getSort().getName().equals("Int")) {
			if (!a.isIntegral()) {
				final BigInteger denom = a.denominator();
				a = a.mul(denom);
				b = b.mul(denom);
				c = c.mul(denom);
			}
			if (!c.isIntegral()) {
				final BigInteger denom = c.denominator();
				a = a.mul(denom);
				b = b.mul(denom);
				c = c.mul(denom);
			}
		} else if (s.getName().equals("Int")) {
			s = sort("Real");
		}
		final Term at = a.toTerm(s), bt = b.toTerm(s), ct = c.toTerm(s);
		// Check implication
		if (mSolverOptions.getCheckType() == CheckType.FULL) {
			// This version only works with full checks. If we forbid case
			// splits, we cannot refute the disjunction created by this method.
			final Term[] disj = new Term[x.length];
			for (int i = 0; i < x.length; ++i) {
				disj[i] = term("not", term("=", term("*", at, x[i]), term("+", term("*", bt, y[i]), ct)));
			}
			try {
				push(1);
				assertTerm(term("or", disj));
				final LBool isImplied = checkSat();
				if (isImplied != LBool.UNSAT) {
					return new Term[] {};
				}
			} finally {
				pop(1);
			}
		} else {
			// This method works for all modes
			for (int i = 0; i < x.length; ++i) {
				final Term neq = term("not", term("=", term("*", at, x[i]), term("+", term("*", bt, y[i]), ct)));
				try {
					push(1);
					assertTerm(neq);
					final LBool isImplied = checkSat();
					if (isImplied != LBool.UNSAT) {
						return new Term[] {};
					}
				} finally {
					pop(1);
				}
			}
		}
		return new Term[] { at, bt, ct };
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		final Sort realSort = resultSort.getRealSort();
		if (realSort.isArraySort() && realSort.getArguments()[0] == getTheory().getBooleanSort()) {
			throw new UnsupportedOperationException("SMTInterpol does not support Arrays with Boolean indices");
		}
		super.declareFun(fun, paramSorts, resultSort);
	}

	private final boolean getBooleanOption(final String option) {
		return (Boolean) mOptions.get(option);
	}

	public boolean isTerminationRequested() {
		return mResourceLimit.isTerminationRequested();
	}

	/**
	 * Use with caution.
	 */
	public void setTerminationRequest(final TerminationRequest request) {
		mCancel = request;
		mTimeout = new TimeoutHandler(request);
		mResourceLimit = new ResourceLimit(mTimeout);
	}

	/**
	 * Use with caution.
	 */
	public TerminationRequest getTerminationRequest() {
		return mCancel;
	}
}
