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
import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.SimpleLayout;
import org.apache.log4j.WriterAppender;

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
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Main;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.SymbolChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.SymbolCollector;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTermGenerator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.PropProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.UnsatCoreCollector;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;

/**
 * Implementation of the 
 * {@link de.uni_freiburg.informatik.ultimate.logic.Script} interface to
 * interact with SMTInterpol.
 * 
 * Users should however stick to the
 * {@link de.uni_freiburg.informatik.ultimate.logic.Script} interface which
 * provides most of the methods provided in this class.
 * @author Juergen Christ
 */
public class SMTInterpol extends NoopScript {
	
	private static class TimeoutHandler implements TerminationRequest {
		TerminationRequest mStackedCancellation;
		long mTimeout;
		
		public TimeoutHandler(TerminationRequest stacked) {
			mStackedCancellation = stacked;
			clearTimeout();
		}
		
		public void clearTimeout() {
			mTimeout = Long.MAX_VALUE;
		}
		
		public void setTimeout(long millis) {
			mTimeout = System.currentTimeMillis() + millis;
		}
		
		public boolean isTerminationRequested() {
			if (mStackedCancellation != null
				&& mStackedCancellation.isTerminationRequested())
				return true;
			return System.currentTimeMillis() >= mTimeout;
		}
	}
	
	private static enum CheckType {
		FULL {
			boolean check(DPLLEngine engine) {
				engine.provideCompleteness(DPLLEngine.COMPLETE);
				return engine.solve();
			}
		},
		PROPAGATION {
			boolean check(DPLLEngine engine) {
				engine.provideCompleteness(DPLLEngine.INCOMPLETE_CHECK);
				return engine.propagate();
			}
		},
		QUICK {
			boolean check(DPLLEngine engine) {
				engine.provideCompleteness(DPLLEngine.INCOMPLETE_CHECK);
				return engine.quickCheck();
			}
		};
		abstract boolean check(DPLLEngine engine);

		public static final CheckType fromOption(Option o, Object value) {
			try {
				return CheckType.valueOf(
								o.checkArg(value, ""/*dummy*/).toUpperCase());
			} catch (IllegalArgumentException eiae) {
				// The enum constant is not present
				StringBuilder sb = new StringBuilder(53);// Should fit exactly
				sb.append("Illegal value. Only ");
				String sep = "";
				for (CheckType t : CheckType.values()) {
					sb.append(sep).append(t.name().toLowerCase());
					sep = ", ";
				}
				sb.append(" allowed.");
				throw new SMTLIBException(sb.toString());
			}
		}
	}
	
	private static class SMTInterpolSetup extends Theory.SolverSetup {
		
		private static class RewriteProofFactory extends FunctionSymbolFactory {
			Sort mProofSort;
			public RewriteProofFactory(String name, Sort proofSort) {
				super(name);
				mProofSort = proofSort;
			}

			@Override
			public int getFlags(
					BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
				return paramSorts.length == 1 ?  FunctionSymbol.INTERNAL
						: FunctionSymbol.LEFTASSOC | FunctionSymbol.INTERNAL;
			}

			@Override
			public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
					Sort resultSort) {
				if (indices != null
					|| paramSorts.length == 0 || paramSorts.length > 2	
					|| resultSort != null
					|| paramSorts[0] != mProofSort)
					return null;

				if (paramSorts.length == 2 && paramSorts[0] != paramSorts[1])
					return null;
				
				return paramSorts[0];
			}
		}
		
		private final int mProofMode;
		
		public SMTInterpolSetup(int proofMode) {
			mProofMode = proofMode;
		}

		@Override
		public void setLogic(Theory theory, Logics logic) {
			int leftassoc = FunctionSymbol.LEFTASSOC;
			// Damn Java compiler...
			Sort proof = null;
			Sort[] proof2 = null;
			Sort bool = theory.getSort("Bool");
			Sort[] bool1 = {bool};
			if (mProofMode > 0) {
				// Partial proofs.
				// Declare all symbols needed for proof production
				declareInternalSort(theory, "@Proof", 0, 0);
				proof = theory.getSort("@Proof");
				proof2 = new Sort[] { proof, proof };
				declareInternalFunction(
						theory, "@res", proof2, proof, leftassoc);
				declareInternalFunction(theory, "@tautology", bool1, proof, 0);
				declareInternalFunction(theory, "@lemma", bool1, proof, 0);
				declareInternalFunction(theory, "@asserted", bool1, proof, 0);
			}
			if (mProofMode > 1) {
				// Full proofs.
				declareInternalFunction(theory, "@intern", bool1, proof, 0);
				declareInternalFunction(
						theory, "@split", new Sort[] {proof, bool}, proof, 0);
				defineFunction(theory, new RewriteProofFactory("@eq", proof));
				declareInternalFunction(theory, "@rewrite", bool1, proof, 0);
				declareInternalFunction(
						theory, "@clause", new Sort[] {proof, bool}, proof, 0);
			}
			defineFunction(theory, new FunctionSymbolFactory("@undefined") {
				
				@Override
				public int getFlags(
						BigInteger[] indices, Sort[] paramSorts, Sort resultSort) {
					return FunctionSymbol.INTERNAL | FunctionSymbol.RETURNOVERLOAD;
				}
				@Override
				public Sort getResultSort(BigInteger[] indices, Sort[] paramSorts,
						Sort resultSort) {
					if (indices != null || paramSorts.length != 0)
						return null;
					return resultSort;
				}
			});
			if (logic.isArray())
				declareArraySymbols(theory);
			if (logic.hasIntegers())
				declareIntSymbols(theory);
			if (logic.hasReals())
				declareRealSymbols(theory);
		}
		
		private final void declareIntSymbols(Theory theory) {
			Sort intSort = theory.getSort("Int");
			Sort[] sort1 = {intSort};
			declareInternalFunction(theory, "@mod0", sort1, intSort, 0);
			declareInternalFunction(theory, "@div0", sort1, intSort, 0);
		}
		
		private final void declareRealSymbols(Theory theory) {
			Sort realSort = theory.getSort("Real");
			Sort[] sort1 = {realSort};
			declareInternalFunction(theory, "@/0", sort1, realSort, 0);
		}
		
		private final void declareArraySymbols(Theory theory) {
			// Currently only diff
			Sort[] vars = theory.createSortVariables("Index", "Elem");
			Sort array = theory.getSort("Array", vars);
			declareInternalPolymorphicFunction(
					theory, "@diff", vars, new Sort[]{array, array}, vars[0], 0);
		}
	}
	
	private static abstract class Option {
		private final String mOptName;
		private final String mDescription;
		private final boolean mOnlineModifyable;
		private final int mOptNum;
		public Option(String optName, String description,
				boolean onlineModifyable, int optnum) {
			mOptName = optName;
			mDescription = description;
			mOnlineModifyable = onlineModifyable;
			mOptNum = optnum;
			SMTInterpol.OPTIONS.add(this);
		}
		public String getName() {
			return mOptName;
		}
		public String getDescription() {
			return mDescription;
		}
		public boolean isOnlineModifyable() {
			return mOnlineModifyable;
		}
		public int getOptionNumber() {
			return mOptNum;
		}
		public abstract <T> T checkArg(Object value, T curval)
			throws SMTLIBException;
	}
	private static class BoolOption extends Option {
		public BoolOption(String optName, String description,
				boolean onlineModifyable, int optnum) {
			super(optName, description, onlineModifyable, optnum);
		}
		public Boolean checkArg(Object value) throws SMTLIBException {
			if (value instanceof Boolean)
				return (Boolean) value;
			if (value instanceof String) {
				if (value.equals("false"))
					return Boolean.FALSE; 
				if (value.equals("true"))
					return Boolean.TRUE;
			}
			throw new SMTLIBException("Option " + getName()
			        + " expects a Boolean value");
		}
		@SuppressWarnings("unchecked")
		@Override
		public <T> T checkArg(Object value, T curval) throws SMTLIBException {
			if (curval instanceof Boolean)
				return (T) checkArg(value);
			throw new SMTLIBException("Option " + getName()
				+ " expects a Boolean value");
		}
	}
	private static class IntOption extends Option {
		public IntOption(String optName, String description,
				boolean onlineModifyable, int optnum) {
			super(optName, description, onlineModifyable, optnum);
		}
		public BigInteger checkArg(Object value) throws SMTLIBException {
			if (value instanceof BigInteger)
				return (BigInteger) value;
			if (value instanceof Long)
				return BigInteger.valueOf((Long) value);
			if (value instanceof Integer)
				return BigInteger.valueOf((Integer) value);
			if (value instanceof String) {
				try {
					return new BigInteger((String) value);
				} catch (NumberFormatException ignored) { 
					/* fall through into error case */
				}
			}
			throw new SMTLIBException("Option " + getName()
					+ " expects a numeral value");
		}
		@SuppressWarnings("unchecked")
		@Override
		public <T> T checkArg(Object value, T curval) throws SMTLIBException {
			if (curval instanceof BigInteger || curval instanceof Integer
					|| curval instanceof Long)
				return (T) checkArg(value);
			throw new SMTLIBException("Option " + getName()
				+ " expects a numeral value");
		}
	}
	private static class StringOption extends Option {
		public StringOption(String optName, String description,
				boolean onlineModifyable, int optnum) {
			super(optName, description, onlineModifyable, optnum);
		}
		public String checkArg(Object value) throws SMTLIBException {
			if (value instanceof String)
				return (String) value;
			throw new SMTLIBException("Option " + getName()
					+ " expects a string value");
		}
		@SuppressWarnings("unchecked")
		@Override
		public <T> T checkArg(Object value, T curval) throws SMTLIBException {
			if (curval instanceof String)
				return (T) checkArg(value);
			throw new SMTLIBException("Option " + getName()
				+ " expects a string value");
		}
	}
	private static class OptionMap {
		private Option[] mOptions;
		private int mNumOptions;
		public OptionMap() {
			mOptions = new Option[0x20];
			mNumOptions = 0;
		}
		private void grow() {
			Option[] oldOptions = mOptions;
			mOptions = new Option[mOptions.length * 2];
			for (Option o : oldOptions)
				add_internal(o);
		}
		public void add(Option option) {
			if (++mNumOptions > mOptions.length)
				grow();
			add_internal(option);
		}
		private void add_internal(Option o) {
			int hash = o.getName().hashCode();
			for (int i = 0; i < mOptions.length; ++i) {
				int idx = (hash + i) & (mOptions.length - 1);
				if (mOptions[idx] == null) {
					mOptions[idx] = o;
					return;
				}
			}
			throw new AssertionError("Did not find empty slot");
		}
		public Option find(String name) {
			int hash = name.hashCode();
			for (int i = 0; i < mNumOptions; ++i) {
				int idx = (hash + i) & (mOptions.length - 1);
				if (mOptions[idx] == null)
					return null;
				String optname = mOptions[idx].getName();
				if (optname.hashCode() == hash && optname.equals(name))
					return mOptions[idx];
			}
			return null;
		}
		public String[] getOptionNames() {
			String[] res = new String[mNumOptions];
			int pos = 0;
			for (Option o : mOptions) {
				if (o != null) {
					res[pos] = o.getName();
					if (++pos == mNumOptions)
						return res;
				}
			}
			// Should never be reached
			return res;
		}
	}
	
	private CheckType mCheckType = CheckType.FULL;
	private DPLLEngine mEngine;
	private Clausifier mClausifier;
	private ScopedArrayList<Term> mAssertions;
	private final TimeoutHandler mCancel;
	
	private String mOutName = "stdout";
	private PrintWriter mErr = new PrintWriter(System.err);
	private String mErrName = "stderr";
	private SimpleLayout mLayout;
	private Logger mLogger;
	private WriterAppender mAppender;
	
	String mErrorMessage;
	boolean mProduceModels = false;
	long mRandomSeed = Config.RANDOM_SEED;
	boolean mProduceProofs = false;
	boolean mProduceUnsatCores = false;
	boolean mProduceAssignment = false;
	boolean mProduceInterpolants = false;
	/**
	 * Current state of the option :print-success. If this is false,
	 * the success output of the commands are not printed.
	 */
	boolean mReportSuccess = true;
	/**
	 * Current state of the option :print-terms-cse.  If this is 
	 * true common subexpressions in output are eliminated by lets.
	 */
	boolean mPrintCSE = true;
	
	boolean mInterpolantCheckMode = false;
	boolean mUnsatCoreCheckMode = false;
	boolean mModelCheckMode = false;
	boolean mProofCheckMode = false;
	
	de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model mModel = null;
	private boolean mPartialModels = false;
	
	private final static Object NAME = new QuotedObject("SMTInterpol");
	private final static Object AUTHORS = new QuotedObject(
					"Jochen Hoenicke, Juergen Christ, and Alexander Nutz");
	private final static Object INTERPOLATION_METHOD = new QuotedObject("tree");
	// I assume an initial check s.t. first (get-info :status) returns sat
	private LBool mStatus = LBool.SAT;
	
	// The status set in the benchmark
	private String mStatusSet = null;
	private ReasonUnknown mReasonUnknown = null;
	// Soft timeout for the solver (in milliseconds)
	private long mTimeout;
	
	// The assertion stack was modified after the last check-sat, i.e., the
	// m_status field is not valid and we have to deactivate
	// get-{value,model,interpolants,proof}.
	private boolean mAssertionStackModified = true;
	// The assertion stack level at which the first division-by-0 was
	// encountered.  If it is -1, it means "never"
	private int mBy0Seen = -1;
	
	// The proof transformation currently used.
	private AvailableTransformations mProofTransformation =
		AvailableTransformations.NONE;
	
	private boolean mSimplifyInterpolants = false;
	private CheckType mSimplifyCheckType = CheckType.QUICK;
	private boolean mSimplifyRepeatedly = true;
	
	// The option numbers
	private final static int OPT_PRINT_SUCCESS = 0;
	private final static int OPT_VERBOSITY = 1;
	private final static int OPT_TIMEOUT = 2;
	private final static int OPT_REGULAR_OUTPUT_CHANNEL = 3;
	private final static int OPT_DIAGNOSTIC_OUTPUT_CHANNEL = 4;
	private final static int OPT_PRODUCE_PROOFS = 5;
	private final static int OPT_PRODUCE_MODELS = 6;
	private final static int OPT_PRODUCE_ASSIGNMENTS = 7;
	private final static int OPT_RANDOM_SEED = 8;
	private final static int OPT_INTERACTIVE_MODE = 9;
	private final static int OPT_INTERPOLANT_CHECK_MODE = 10;
	private final static int OPT_PRODUCE_INTERPOLANTS = 11;
	private final static int OPT_PRODUCE_UNSAT_CORES = 12;
	private final static int OPT_UNSAT_CORE_CHECK_MODE = 13;
	private final static int OPT_PRINT_TERMS_CSE = 14;
	private final static int OPT_MODEL_CHECK_MODE = 15;
	private final static int OPT_PROOF_TRANSFORMATION = 16;
	private final static int OPT_MODELS_PARTIAL = 17;
	private final static int OPT_CHECK_TYPE = 18;
	private final static int OPT_SIMPLIFY_INTERPOLANTS = 19;
	private final static int OPT_SIMPLIFY_CHECK_TYPE = 20;
	private final static int OPT_SIMPLIFY_REPEATEDLY = 21;
	private final static int OPT_PROOF_CHECK_MODE = 22;
	//// Add a new option number for every new option
	
	// The Options Map
	private final static OptionMap OPTIONS = new OptionMap();
	
	static {
		new BoolOption(":print-success",
				"Print \"success\" after successfully executing a command",
				true, OPT_PRINT_SUCCESS);
		new IntOption(":verbosity", "Set the verbosity level",
				true, OPT_VERBOSITY);
		new IntOption(":timeout", "Set the timeout", true, OPT_TIMEOUT);
		new StringOption(":regular-output-channel",
				"Configure the standard output channel",
				true, OPT_REGULAR_OUTPUT_CHANNEL);
		new StringOption(":diagnostic-output-channel",
				"Configure the debug output channel",
				true, OPT_DIAGNOSTIC_OUTPUT_CHANNEL);
		new BoolOption(":produce-proofs",
				"Generate proofs (needed for interpolants)",
				false, OPT_PRODUCE_PROOFS);
		new BoolOption(":produce-models", "Produce models",
				true, OPT_PRODUCE_MODELS);
		new BoolOption(":produce-assignments",
				"Produce assignments for named Boolean terms",
				false, OPT_PRODUCE_ASSIGNMENTS);
		new IntOption(":random-seed", "Set the random seed",
				true, OPT_RANDOM_SEED);
		new BoolOption(":interactive-mode", "Cache all asserted terms",
				false, OPT_INTERACTIVE_MODE);
		new BoolOption(":interpolant-check-mode",
				"Check generated interpolants",
				false, OPT_INTERPOLANT_CHECK_MODE);
		new BoolOption(":produce-unsat-cores", "Enable unsat core generation",
				false, OPT_PRODUCE_UNSAT_CORES);
		new BoolOption(":unsat-core-check-mode", "Check generated unsat cores",
				false, OPT_UNSAT_CORE_CHECK_MODE);
		new BoolOption(":print-terms-cse",
				"Eliminate common subexpressions in output",
				true, OPT_PRINT_TERMS_CSE);
		new BoolOption(":model-check-mode",
				"Check satisfiable formulas against the produced model",
				false, OPT_MODEL_CHECK_MODE);
		new StringOption(":proof-transformation",
				"Algorithm used to transform the resolution proof tree", true,
				OPT_PROOF_TRANSFORMATION);
		new BoolOption(":produce-interpolants", "Enable interpolant production",
				false, OPT_PRODUCE_INTERPOLANTS);
		new BoolOption(":partial-models", "Don't totalize models", true,
				OPT_MODELS_PARTIAL);
		new StringOption(":check-type",
				"Strength of check used in check-sat command", true,
				OPT_CHECK_TYPE);
		new BoolOption(":simplify-interpolants",
				"Apply strong context simplification to computed interpolants",
				true, OPT_SIMPLIFY_INTERPOLANTS);
		new StringOption(":simplify-check-type",
				"Strength of check used in simplify command", true,
				OPT_SIMPLIFY_CHECK_TYPE);
		new BoolOption(":simplify-repeatedly",
				"Simplify until the fixpoint is reached", true,
				OPT_SIMPLIFY_REPEATEDLY);
		new BoolOption(":proof-check-mode",
				"Check the produced proof for unsatisfiable formulas", false,
				OPT_PROOF_CHECK_MODE);
		//// Create new option object for every new option
	}
	
	/**
	 * Delta debugger friendly version.  Exits with following codes:
	 * model-check-mode fails: 1
	 * interpolant-check-mode fails: 2
	 * exception during check-sat: 3
	 * command that needed sat after last check got unsat: 4
	 * command that needed unsat after last check got sat: 5
	 */
	private final boolean mDDFriendly =
	        !Config.COMPETITION 
			    && System.getProperty("smtinterpol.ddfriendly") != null;
	
	/**
	 * Default constructor using the root logger and no user termination
	 * request.  If this constructor is used, SMTInterpol assumes ownership of
	 * the logger.
	 */
	public SMTInterpol() {
		this(Logger.getRootLogger(), true, null);
	}
	
	/**
	 * Construct SMTInterpol with a user-owned logger but without user
	 * termination request.  Note that the logger is assumed to be correctly set
	 * up.
	 * @param logger The logger owned by the caller.
	 */
	public SMTInterpol(Logger logger) {
		this(logger, false, null);
	}
	
	/**
	 * Construct SMTInterpol with a but without user termination request.  The
	 * logger has to be set up correctly if SMTInterpol should not take
	 * ownership of it.
	 * @param logger    The logger owned by the caller.
	 * @param ownLogger Should SMTInterpol take ownership of the logger?
	 */
	public SMTInterpol(Logger logger, boolean ownLogger) {
		this(logger, ownLogger, null);
	}
	
	/**
	 * Default constructor using the root logger and a given user termination
	 * request.  If this constructor is used, SMTInterpol assumes ownership of
	 * the logger.
	 * @param cancel User termination request to poll during checks.
	 */
	public SMTInterpol(TerminationRequest cancel) {
		this(Logger.getRootLogger(), true, cancel);
	}
	
	/**
	 * Construct SMTInterpol with a user-owned logger and a user termination
	 * request.  Note that the logger is assumed to be correctly set up.
	 * @param logger The logger owned by the caller.
	 * @param cancel User termination request to poll during checks.
	 */
	public SMTInterpol(Logger logger, TerminationRequest cancel) {
		this(logger, false, cancel);
	}
	
	/**
	 * Construct SMTInterpol with a user-owned logger but without user
	 * termination request.  Note that the logger is assumed to be correctly set
	 * up.
	 * @param logger    The logger owned by the caller.
	 * @param ownLogger Should SMTInterpol take ownership of the logger?
	 * @param cancel    User termination request to poll during checks.
	 */
	public SMTInterpol(
			Logger logger, boolean ownLogger, TerminationRequest cancel) {
		mLogger = logger;
		if (ownLogger) {
			mLayout = new SimpleLayout();
			mAppender = new WriterAppender(mLayout, mErr);
			mLogger.addAppender(mAppender);
			mLogger.setLevel(Config.DEFAULT_LOG_LEVEL);
		}
		mTimeout = 0;
		mCancel = new TimeoutHandler(cancel);
		reset();
	}
	/**
	 * Copy the current context and modify some pre-theory options.  The copy
	 * shares the push/pop stack on the symbols but not on the assertions.
	 * Users should be careful not to mess up the push/pop stack, i.e., not to
	 * push on one context and pop on another one.
	 * 
	 * Note that this cloning does not clone the assertion stack and should not
	 * be used in multi-threaded contexts since users cannot guarantee correct
	 * push/pop-stack treatment.
	 * @param other   The context to clone.
	 * @param options The options to set before setting the logic.
	 */
	public SMTInterpol(SMTInterpol other, Map<String, Object> options) {
		super(other.getTheory());
		mLogger = other.mLogger;
		mTimeout = other.mTimeout;
		if (options != null)
			for (Map.Entry<String, Object> me : options.entrySet())
				setOption(me.getKey(), me.getValue());
		mCancel = other.mCancel;
		setupClausifier(getTheory().getLogic());
	}
	
	// Called in ctor => make it final
	/**
	 * Unset the logic and clear the assertion stack.  This does not reset
	 * online modifyable options.
	 */
	public final void reset() {
		super.reset();
		mEngine = null;
		mModel = null;
		mAssertionStackModified = true;
        if (mAssertions != null)
        	mAssertions.clear();
	}
	
	@Override
	public void push(int n) throws SMTLIBException {
		super.push(n);
		modifyAssertionStack();
		while (n-- > 0) {
			if (mAssertions != null)
				mAssertions.beginScope();
			mClausifier.push();
		}
	}
	
	@Override
	public void pop(int n) throws SMTLIBException {
		try {
			super.pop(n);
		} catch (SMTLIBException eBug) {
			if (mDDFriendly)
				System.exit(123);
			throw eBug;
		}
		modifyAssertionStack();
		int i = n;
		while (i-- > 0) {
			if (mAssertions != null)
				mAssertions.endScope();
		}
		mClausifier.pop(n);
		if (mStackLevel < mBy0Seen)
			// We've popped all division-by-0s.
			mBy0Seen = -1;
	}
	
	@Override
	public LBool checkSat() throws SMTLIBException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		mModel = null;
		mAssertionStackModified = false;
		if (mTimeout > 0) {
			mCancel.setTimeout(mTimeout);
		}
		
		LBool result = LBool.UNKNOWN;
		mReasonUnknown = ReasonUnknown.INCOMPLETE;
		mEngine.setRandomSeed(mRandomSeed);
		try {
			if (mCheckType.check(mEngine)) {
				if (mEngine.hasModel()) {
					result = LBool.SAT;
					if (mModelCheckMode/* && m_ProduceModels*/) {
						mModel = new de.uni_freiburg.informatik.ultimate.
								smtinterpol.model.Model(
								mClausifier, getTheory(), mPartialModels);
						if (!mModel.checkTypeValues(mLogger) && mDDFriendly)
							System.exit(1);
						for (Term asserted : mAssertions) {
							Term checkedResult = mModel.evaluate(asserted);
							if (checkedResult != getTheory().mTrue) {
								if (mDDFriendly)
									System.exit(1);
								mLogger.fatal("Model does not satisfy " 
										+ asserted.toStringDirect());
//								for (Term t : getSatisfiedLiterals())
//									if (m_Model.evaluate(t) != getTheory().TRUE)
//										m_Logger.fatal("Unsat lit: " + t.toStringDirect());
							}
						}
					}
				} else {
					result = LBool.UNKNOWN;
					switch(mEngine.getCompleteness()) {
					case DPLLEngine.COMPLETE:
						if (mCheckType == CheckType.FULL)
							throw new InternalError("Complete but no model?");
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
					mLogger.info(
							new DebugMessage(
									"Got {0} as reason to return unknown",
									mEngine.getCompletenessReason()));
				}
			} else {
				result = LBool.UNSAT;
				if (mProofCheckMode) {
					ProofChecker proofchecker = 
							new ProofChecker(this, getLogger());
					if (!proofchecker.check(getProof())) { 
						if (mDDFriendly)
							System.exit(2);
						mLogger.fatal("Proof-checker did not verify");
					}
				}
			}
		} catch (OutOfMemoryError eoom) {
			// BUGFIX: Don't do this since log4j will produce another OOM.
//			m_Logger.fatal("OOM during check ",oom);
			mReasonUnknown = ReasonUnknown.MEMOUT;
		} catch (Throwable ex) {
			if (mDDFriendly)
				System.exit(3);// NOCHECKSTYLE
			mLogger.fatal("Error during check ",ex);
			mReasonUnknown = ReasonUnknown.CRASHED;
		}
		mStatus = result;
		if (Config.CHECK_STATUS_SET && isStatusSet() 
				&& mReasonUnknown != ReasonUnknown.MEMOUT
					&& !mStatus.toString().equals(mStatusSet)) {
			mLogger.warn("Status differs: User said " + mStatusSet
					+ " but we got " + mStatus);
			if (mDDFriendly)
				System.exit(13);
		}
		mStatusSet = null;
		mCancel.clearTimeout();
		return result;
	}
	
	private final boolean isStatusSet() {
		return mStatusSet != null && !mStatusSet.equals("unknown");
	}

	@Override
	public void setLogic(String logic)
	    throws UnsupportedOperationException, SMTLIBException {
		try {
			setLogic(Logics.valueOf(logic));
		} catch (IllegalArgumentException ex) {
			/* Logic is not in enumeration */
			throw new 
			UnsupportedOperationException("Logic " + logic + " not supported");
		}
	}
	
	@Override
	public void setLogic(Logics logic)
		throws UnsupportedOperationException, SMTLIBException {
		mSolverSetup = new SMTInterpolSetup(getProofMode());
		super.setLogic(logic);
		setupClausifier(logic);
	}

	/**
	 * Setup the clausifier and the engine according to the logic,
	 * the current proof production mode, and some other options.
	 * @param logic the SMT-LIB logic to use.
	 * @throws UnsupportedOperationException if the logic is not supported
	 * by SMTInterpol.
	 */
	private void setupClausifier(Logics logic) {
		try {
			int proofMode = getProofMode();
			mEngine = new DPLLEngine(getTheory(), mLogger, mCancel);
			mClausifier = new Clausifier(mEngine, proofMode);
			// This has to be before set-logic since we need to capture
			// initialization of CClosure.
			mEngine.setProofGeneration(proofMode > 0);
			mClausifier.setLogic(logic);
			mClausifier.setAssignmentProduction(mProduceAssignment);
			mEngine.setProduceAssignments(mProduceAssignment);
			mEngine.setRandomSeed(mRandomSeed);
		} catch (UnsupportedOperationException eLogicUnsupported) {
			super.reset();
			mEngine = null;
			mClausifier = null;
			throw eLogicUnsupported;
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		super.assertTerm(term);
		if (!term.getSort().equals(getTheory().getBooleanSort())) {
			if (term.getSort().getTheory() == getTheory())
				throw new SMTLIBException("Asserted terms must have sort Bool");
			else
				throw new SMTLIBException("Asserted terms created with incompatible theory");
		}
		if (Config.STRONG_USAGE_CHECKS && !new CheckClosedTerm().isClosed(term))
			throw new SMTLIBException("Asserted terms must be closed");
		if (mAssertions != null)
			mAssertions.add(term);
		if (mEngine.inconsistent()) {
			mLogger.info("Asserting into inconsistent context");
			return LBool.UNSAT;
		}
		try {
			modifyAssertionStack();
			mClausifier.addFormula(term);
			/* We always have to reset the flag, but only need to set the stack
			 * level if it is not already set. 
			 */
			if (mClausifier.resetBy0Seen() && mBy0Seen == -1)
				mBy0Seen = mStackLevel;
			if (!mEngine.quickCheck()) {
				mLogger.info("Assertion made context inconsistent");
				return LBool.UNSAT;
			}
		} catch (UnsupportedOperationException ex) {
			throw new SMTLIBException(ex.getMessage());
		} catch (RuntimeException exc) {
			if (mDDFriendly)
				System.exit(7);// NOCHECKSTYLE
			throw exc;
		} catch (AssertionError exc) {
			if (mDDFriendly)
				System.exit(7);// NOCHECKSTYLE
			throw exc;
		}
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		if (mAssertions != null)
			return mAssertions.toArray(new Term[mAssertions.size()]);
		throw new SMTLIBException(
				"Set option :interactive-mode to true to get assertions!");
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		if (!mEngine.isProduceAssignments())
			throw new SMTLIBException(
				"Set option :produce-assignments to true to generate assignments!");
		checkAssertionStackModified();
		return mEngine.getAssignments();
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		if (":status".equals(info))
			return mStatus;
		if (":name".equals(info))
			return NAME;
		if (":version".equals(info))
			return new QuotedObject(Main.getVersion());
		if (":authors".equals(info))
			return AUTHORS;
		if (":all-statistics".equals(info)) {
			return mEngine == null ? new Object[0] : mEngine.getStatistics();
		}
		if (":status-set".equals(info))
			return mStatusSet;
		if (":options".equals(info)) {
			return OPTIONS.getOptionNames();
		}
		if (":reason-unknown".equals(info)) {
			if (mStatus != LBool.UNKNOWN)
				throw new SMTLIBException("Status not unknown");
			return mReasonUnknown;
		}
		if (":assertion-stack-levels".equals(info))
			return mStackLevel;
		// Info from our SMTLIB interpolation proposal
		if (":interpolation-method".equals(info))
			return INTERPOLATION_METHOD;
		Option opt = OPTIONS.find(info);
		if (opt != null) {
			if (opt.isOnlineModifyable()) {
				return new Object[] { 
					":description",
					new QuotedObject(opt.getDescription()),
					":online-modifyable" };
			}
			return new Object[] {
				":description", new QuotedObject(opt.getDescription()) };
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		Option o = OPTIONS.find(opt);
		if (o == null)
			throw new UnsupportedOperationException();
		switch (o.getOptionNumber()) {
		case OPT_PRINT_SUCCESS:
			return mReportSuccess;
		case OPT_VERBOSITY:
			switch(mLogger.getLevel().toInt()) {
			case Level.ALL_INT:
				return BigInteger.valueOf(6); // NOCHECKSTYLE
			case Level.DEBUG_INT:
				return BigInteger.valueOf(5); // NOCHECKSTYLE
			case Level.INFO_INT:
				return BigInteger.valueOf(4); // NOCHECKSTYLE
			case Level.WARN_INT:
				return BigInteger.valueOf(3); // NOCHECKSTYLE
			case Level.ERROR_INT:
				return BigInteger.valueOf(2);
			case Level.FATAL_INT:
				return BigInteger.valueOf(1);
			default:
				return BigInteger.valueOf(0);
			}
		case OPT_TIMEOUT:
			return BigInteger.valueOf(mTimeout);
		case OPT_REGULAR_OUTPUT_CHANNEL:
			return mOutName;
		case OPT_DIAGNOSTIC_OUTPUT_CHANNEL:
			return mErrName;
		case OPT_PRODUCE_PROOFS:
			return mProduceProofs;
		case OPT_PRODUCE_MODELS:
			return mProduceModels;
		case OPT_PRODUCE_ASSIGNMENTS:
			return mProduceAssignment;
		case OPT_RANDOM_SEED:
			return BigInteger.valueOf(mRandomSeed);
		case OPT_INTERACTIVE_MODE:
			return mAssertions != null;
		case OPT_INTERPOLANT_CHECK_MODE:
			return mInterpolantCheckMode;
		case OPT_PRODUCE_UNSAT_CORES:
			return mProduceUnsatCores;
		case OPT_UNSAT_CORE_CHECK_MODE:
			return mUnsatCoreCheckMode;
		case OPT_PRINT_TERMS_CSE:
			return mPrintCSE;
		case OPT_MODEL_CHECK_MODE:
			return mModelCheckMode;
		case OPT_PROOF_TRANSFORMATION:
			return mProofTransformation.name();
		case OPT_PRODUCE_INTERPOLANTS:
			return mProduceInterpolants;
		case OPT_MODELS_PARTIAL:
			return mPartialModels;
		case OPT_CHECK_TYPE:
			return mCheckType.name().toLowerCase();
		case OPT_SIMPLIFY_INTERPOLANTS:
			return mSimplifyInterpolants;
		case OPT_SIMPLIFY_CHECK_TYPE:
			return mSimplifyCheckType.name().toLowerCase();
		case OPT_SIMPLIFY_REPEATEDLY:
			return mSimplifyRepeatedly;
		case OPT_PROOF_CHECK_MODE:
			return mProofCheckMode;
		default:
			throw new InternalError("This should be implemented!!!");
		}
	}

	/**
	 * Get the proofMode according to the options that are set.
	 * @returns 2 for full proofs, 1 for propositional only proofs, 0
	 * for no proofs.
	 */
	private int getProofMode() {
		if (mProofCheckMode || mProduceProofs) {
			return 2;
		} else if (mProduceInterpolants || mProduceUnsatCores) { 
			return 1;
		} else {
			return 0;
		}
	}
	
	@Override
	public Term getProof()
	    throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		int proofMode = getProofMode();
		if (proofMode == 0)
			throw new SMTLIBException("Option :produce-proofs not set to true");
		if (proofMode == 1)
			mLogger.warn("Using partial proofs (cut at CNF-level).  "
				+ "Set option :produce-proofs to true to get complete proofs."
			);
		checkAssertionStackModified();
		Clause unsat = retrieveProof();
		if (Config.CHECK_PROP_PROOF) {
			PropProofChecker ppc = new PropProofChecker();
			boolean correct = ppc.check(unsat);
			assert correct;
		}
		try {
			ProofTermGenerator generator = new ProofTermGenerator(getTheory());
			Term res = generator.convert(retrieveProof());
			if (mBy0Seen != -1)
				res = new Div0Remover().transform(res);
			return res;
		} catch (Exception exc) {	
			throw new SMTLIBException(exc.getMessage() == null 
					? exc.toString() : exc.getMessage());
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree) {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		if (!mProduceProofs && !mProduceInterpolants)
			throw new SMTLIBException(
					"Interpolant production not enabled.  Set either :produce-interpolants or :produce-proofs to true");
		if (mTimeout > 0) {
			mCancel.setTimeout(mTimeout);
		}
		try {
		checkAssertionStackModified();
		if (partition.length != startOfSubtree.length)
			throw new SMTLIBException(
			    "Partition table and subtree array need to have equal length");
		if (Config.STRONG_USAGE_CHECKS) {
			for (int i = 0; i < partition.length; i++) {
				if (startOfSubtree[i] < 0)
					throw new SMTLIBException(
					    "subtree array must not contain negative element");
				int j = i;
				while (startOfSubtree[i] < j)
					j = startOfSubtree[j - 1];
				if (startOfSubtree[i] != j)
					throw new SMTLIBException("malformed subtree array.");
			}
			if (startOfSubtree[partition.length - 1] != 0)
				throw new SMTLIBException("malformed subtree array.");
		}
		Set<String>[] parts = new Set[partition.length];
		String errormsg = 
			"arguments must be named terms or conjunctions of named terms";
		for (int i = 0; i < partition.length; i++) {
			if (!(partition[i] instanceof ApplicationTerm)) {
				throw new SMTLIBException(errormsg);
			}
			FunctionSymbol fsym = ((ApplicationTerm) partition[i]).getFunction();
			Term[] terms;
			if (fsym.isIntern()) {
				if (!fsym.getName().equals("and"))
					throw new SMTLIBException(errormsg);
				terms = ((ApplicationTerm) partition[i]).getParameters();
			} else
				terms = new Term[] { partition[i] };
			parts[i] = new HashSet<String>();
			for (int j = 0; j < terms.length; j++) {
				if (!(terms[j] instanceof ApplicationTerm)) {
					throw new SMTLIBException(errormsg);
				}
				ApplicationTerm appTerm = (ApplicationTerm) terms[j];
				if (appTerm.getParameters().length != 0)
					throw new SMTLIBException(errormsg);
				if (appTerm.getFunction().isIntern())
					throw new SMTLIBException(errormsg);
				parts[i].add(appTerm.getFunction().getName().intern());
			}
		}
		SMTInterpol tmpBench = null;
		SymbolCollector collector = null;
		Set<FunctionSymbol> globals = null;
		if (mInterpolantCheckMode) {
			HashSet<String> usedParts = new HashSet<String>();
			for (Set<String> part : parts)
				usedParts.addAll(part);
			tmpBench = new SMTInterpol(this,
					Collections.singletonMap(":interactive-mode",
							(Object)Boolean.TRUE));
			Level old = tmpBench.mLogger.getLevel();
			try {
				tmpBench.mLogger.setLevel(Level.ERROR);
				// Clone the current context except for the parts used in the
				// interpolation problem
				collector = new SymbolCollector();
				collector.startCollectTheory();
			termloop: 
			    for (Term asserted : mAssertions) {
					if (asserted instanceof AnnotatedTerm) {
						AnnotatedTerm annot = (AnnotatedTerm) asserted;
						for (Annotation an : annot.getAnnotations()) {
							if (":named".equals(an.getKey()) 
									&& usedParts.contains(an.getValue()))
								continue termloop;
						}
					}
					tmpBench.assertTerm(asserted);
					collector.addGlobalSymbols(asserted);
				}
				globals = collector.getTheorySymbols();
			} finally {
				tmpBench.mLogger.setLevel(old);
			}
			// free space
			usedParts = null;
		}
		Interpolator interpolator =
			new Interpolator(mLogger, this, tmpBench, getTheory(), parts, startOfSubtree);
		Clause refutation = retrieveProof();
		Term[] ipls = interpolator.getInterpolants(refutation);
		
		if (mBy0Seen != -1) {
			Div0Remover rem = new Div0Remover();
			for (int i = 0; i < ipls.length; ++i)
				ipls[i] = rem.transform(ipls[i]);
		}
		
		if (mInterpolantCheckMode) {
			boolean error = false;
			Level old = tmpBench.mLogger.getLevel();
			try {
				tmpBench.mLogger.setLevel(Level.ERROR);
				// Compute Symbol occurrence
				Map<FunctionSymbol, Integer>[] occs =
					new Map[partition.length];
				for (int i = 0; i < partition.length; ++i)
					occs[i] = collector.collect(partition[i]);
				// Recompute the symbol occurrence:
				// occs[i] should be the symbols occurring in the subtree of
				// partition[i]
				for (int i = 0; i < startOfSubtree.length; ++i) {
					// Find children
					int child = i - 1;
					while (child >= startOfSubtree[i]) {
						// join occurrence maps
						for (Map.Entry<FunctionSymbol, Integer> me
						        : occs[child].entrySet()) {
							Integer ival = occs[i].get(me.getKey());
							ival = ival == null ? me.getValue()
								: ival + me.getValue();
							occs[i].put(me.getKey(), ival);
						}
						child = startOfSubtree[child] - 1;
					}
				}
				SymbolChecker checker = new SymbolChecker(globals);
				for (int i = 0; i < startOfSubtree.length; ++i) {
					tmpBench.push(1);
					// Find and assert children
					int child = i - 1;
					while (child >= startOfSubtree[i]) {
						tmpBench.assertTerm(ipls[child]);
						child = startOfSubtree[child] - 1;
					}
					// Assert node
					tmpBench.assertTerm(partition[i]);
					// Assert negated interpolant
					try {
						if (i != ipls.length)
							tmpBench.assertTerm(tmpBench.term("not", ipls[i]));
					} catch (SMTLIBException exc) {
						mLogger.error("Could not assert interpolant", exc);
						error = true;
					}
					LBool res = tmpBench.checkSat();
					if (res == LBool.SAT) {
						if (mDDFriendly)
							System.exit(2);
						mLogger.error(new DebugMessage(
						        "Interpolant {0} not inductive: "
								+ " (Check returned {1})", i, res));
						error = true;
					} else if (res == LBool.UNKNOWN) {
						ReasonUnknown ru = tmpBench.mReasonUnknown;
						mLogger.warn("Unable to check validity of interpolant: "
								+ ru);
						// I don't set the error flag here since I am not sure
						// whether this is a real error or not.  Maybe we should
						// base this on ru?
					}
					tmpBench.pop(1);
					// Check symbol condition
					if (i != ipls.length 
						&& checker.check(ipls[i], occs[i], occs[ipls.length])) {
						mLogger.error(new DebugMessage(
								"Symbol error in Interpolant {0}.  "
								+ "Subtree only symbols: {1}.  "
								+ "Non-subtree only symbols: {2}.", i,
								checker.getLeftErrors(),
								checker.getRightErrors()));
						error = true;
					}
				}
			} finally {
				tmpBench.mLogger.setLevel(old);
				// Not needed for now, but maybe later...
				tmpBench.exit();
			}
			if (error)
				throw new SMTLIBException(
				        "generated interpolants did not pass sanity check");
		}
		if (mSimplifyInterpolants) {
			SimplifyDDA simplifier = new SimplifyDDA(new SMTInterpol(this, 
					Collections.singletonMap(
							":check-type", (Object) mSimplifyCheckType.name())),
							mSimplifyRepeatedly);
			for (int i = 0; i < ipls.length; ++i)
				ipls[i] = simplifier.getSimplifiedTerm(ipls[i]);
		}
		return ipls;
		} finally {
			mCancel.clearTimeout();
		}
	}
	
	@Override
	public Term[] getUnsatCore()
	    throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		if (!mProduceUnsatCores)
			throw new SMTLIBException(
					"Set option :produce-unsat-cores to true before using get-unsat-cores");
		checkAssertionStackModified();
		Clause unsat = mEngine.getProof();
		if (unsat == null)
			throw new SMTLIBException("Logical context not inconsistent!");
		Term[] core = new UnsatCoreCollector(this).getUnsatCore(unsat);
		if (mUnsatCoreCheckMode) {
			HashSet<String> usedParts = new HashSet<String>();
			for (Term t : core)
				usedParts.add(((ApplicationTerm)t).getFunction().getName());
			SMTInterpol tmpBench = new SMTInterpol(this, null);
			Level old = tmpBench.mLogger.getLevel();
			try {
				tmpBench.mLogger.setLevel(Level.ERROR);
				// Clone the current context except for the parts used in
				// the unsat core
			termloop:
			    for (Term asserted : mAssertions) {
					if (asserted instanceof AnnotatedTerm) {
						AnnotatedTerm annot = (AnnotatedTerm) asserted;
						for (Annotation an : annot.getAnnotations()) {
							if (":named".equals(an.getKey()) 
									&& usedParts.contains(an.getValue()))
								continue termloop;
						}
					}
					tmpBench.assertTerm(asserted);
				}
				for (Term t : core)
					tmpBench.assertTerm(t);
				LBool isUnsat = tmpBench.checkSat();
				if (isUnsat != LBool.UNSAT) {
					mLogger.error(new DebugMessage(
							"Unsat core could not be proven unsat (Result is {0})",
							isUnsat));
				}
			} finally {
				tmpBench.mLogger.setLevel(old);
				// Not needed for now, but maybe later...
				tmpBench.exit();
			}
		}
		return core;
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms)
	    throws SMTLIBException, UnsupportedOperationException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		buildModel();
		return mModel.evaluate(terms);
	}
	
	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		if (mEngine == null)
			throw new SMTLIBException("No logic set!");
		buildModel();
		return mModel;
	}

	@Override
	public void setInfo(String info, Object value) {
		if (info.equals(":status")
			&& value instanceof String) {
			if (value.equals("sat")) {
				mStatus = LBool.SAT;
				mStatusSet = "sat";
			} else if (value.equals("unsat")) {
				mStatus = LBool.UNSAT;
				mStatusSet = "unsat";
			} else if (value.equals("unknown")) {
				mStatus = LBool.UNKNOWN;
				mStatusSet = "unknown";
			}
		}
	}
	
	/**
	 * Translates special files names specified by SMTLIB into PrintWriters.
	 * 
	 * The special file names are <pre>stdout</pre> and <pre>stderr</pre>.
	 * @param file Name of a file or a special file name.
	 * @return PrintWriter to write to this file.
	 * @throws IOException Output file could not be opened for writing.
	 */
	public PrintWriter createChannel(String file) throws IOException {
		if (file.equals("stdout"))
			return new PrintWriter(System.out);
		else if (file.equals("stderr"))
			return new PrintWriter(System.err);
		else
			return new PrintWriter(new FileWriter(file));
	}
	
	private final void checkOnlineModifyable(Option opt) throws SMTLIBException {
		if (mEngine != null && !opt.isOnlineModifyable())
			throw new SMTLIBException("Option " + opt.getName() 
					+ " can only be changed before setting the logic");
	}
	
	@Override
	public void setOption(String opt, Object value)
	    throws UnsupportedOperationException, SMTLIBException {
		Option o = OPTIONS.find(opt);
		if (o == null)
			throw new UnsupportedOperationException();
		checkOnlineModifyable(o);
		switch (o.getOptionNumber()) {
		case OPT_PRINT_SUCCESS:
			mReportSuccess = o.checkArg(value, mReportSuccess);
			break;
		case OPT_VERBOSITY:
			BigInteger blevel = o.checkArg(value, BigInteger.ZERO);// FAKE...
			int level = blevel.bitLength() >= 32 ?  // NOCHECKSTYLE
					Integer.MAX_VALUE : blevel.intValue();
			if (level > 5) // NOCHECKSTYLE
				mLogger.setLevel(Level.ALL);
			else if (level > 4) // NOCHECKSTYLE
				mLogger.setLevel(Level.DEBUG);
			else if (level > 3) // NOCHECKSTYLE
				mLogger.setLevel(Level.INFO);
			else if (level > 2)
				mLogger.setLevel(Level.WARN);
			else if (level > 1)
				mLogger.setLevel(Level.ERROR);
			else if (level > 0)
				mLogger.setLevel(Level.FATAL);
			else if (level == -1)
				mLogger.setLevel(Level.TRACE);
			else
				mLogger.setLevel(Level.OFF);
			break;
		case OPT_TIMEOUT:
		{
			BigInteger val = o.checkArg(value, BigInteger.ZERO);// FAKE...
			if (val.signum() == -1)
				mTimeout = 0;
			else if (val.bitLength() < 63) // NOCHECKSTYLE
				mTimeout = val.longValue();
			else
				// Don't think anyone will wait for that time...
				mTimeout = Long.MAX_VALUE;
			break;
		}
		case OPT_REGULAR_OUTPUT_CHANNEL:
			mOutName = o.checkArg(value, mOutName);
			break;
		case OPT_DIAGNOSTIC_OUTPUT_CHANNEL:
			if (mAppender == null)
				throw new SMTLIBException("SMTInterpol does not own the logger");
			try {
				String arg = o.checkArg(value, mErrName);
				mErr = createChannel(arg);
				mAppender.setWriter(mErr);
				mErrName = arg;
			} catch (IOException ex) {
				mLogger.error(ex);
				throw new SMTLIBException("file not found: " + value);
			}
			break;
		case OPT_PRODUCE_PROOFS:
			mProduceProofs = o.checkArg(value, mProduceProofs);
			break;
		case OPT_PRODUCE_MODELS:
			mProduceModels = o.checkArg(value, mProduceModels);
			break;
		case OPT_PRODUCE_ASSIGNMENTS:
			mProduceAssignment = o.checkArg(value, mProduceAssignment);
			break;
		case OPT_RANDOM_SEED:
		{
			BigInteger val = o.checkArg(value, BigInteger.ZERO);//FAKE...
			mRandomSeed = val.bitLength() < 64 ?  // NOCHECKSTYLE
					val.longValue() : Long.MAX_VALUE;
			if (mEngine != null)
				mEngine.setRandomSeed(mRandomSeed);
			break;
		}
		case OPT_INTERACTIVE_MODE:
			if (o.checkArg(value, Boolean.TRUE) == Boolean.TRUE)// FAKE...
				mAssertions = new ScopedArrayList<Term>();
			else if (!mInterpolantCheckMode && !mUnsatCoreCheckMode
					&& !mProofCheckMode)
				mAssertions = null;
			break;
		case OPT_INTERPOLANT_CHECK_MODE:
			if ((mInterpolantCheckMode =
				    o.checkArg(value, mInterpolantCheckMode)) 
				&& mAssertions == null)
					mAssertions = new ScopedArrayList<Term>();
			break;
		case OPT_PRODUCE_UNSAT_CORES:
			mProduceUnsatCores = o.checkArg(value, mProduceUnsatCores);
			break;
		case OPT_UNSAT_CORE_CHECK_MODE:
			if ((mUnsatCoreCheckMode = o.checkArg(value, mUnsatCoreCheckMode))
				 && mAssertions == null)
					mAssertions = new ScopedArrayList<Term>();
			break;
		case OPT_PRINT_TERMS_CSE:
			mPrintCSE = o.checkArg(value, mPrintCSE);
			break;
		case OPT_MODEL_CHECK_MODE:
			if ((mModelCheckMode = o.checkArg(value, mModelCheckMode))
				&& mAssertions == null)
					mAssertions = new ScopedArrayList<Term>();
			break;
		case OPT_PROOF_TRANSFORMATION: {
			String arg = o.checkArg(value, ""); // FAKE dummy
			try {
				AvailableTransformations tmp =
					AvailableTransformations.valueOf(arg);
				mProofTransformation = tmp;
			} catch (IllegalArgumentException eiae) {
				// The enum constant is not present
				StringBuilder sb = new StringBuilder();
				sb.append("Illegal value. Only ");
				String sep = "";
				for (AvailableTransformations a : AvailableTransformations.values()) {
					sb.append(sep).append(a.name());
					sep = ", ";
				}
				sb.append(" allowed.");
				throw new SMTLIBException(sb.toString());
			}
			break;
		}
		case OPT_PRODUCE_INTERPOLANTS:
			mProduceInterpolants = o.checkArg(value, mProduceInterpolants);
			break;
		case OPT_MODELS_PARTIAL:
			mPartialModels = o.checkArg(value, mPartialModels);
			mModel = null;
			break;
		case OPT_CHECK_TYPE:
			mCheckType = CheckType.fromOption(o, value);
			break;
		case OPT_SIMPLIFY_INTERPOLANTS:
			mSimplifyInterpolants = o.checkArg(value, mSimplifyInterpolants);
			break;
		case OPT_SIMPLIFY_CHECK_TYPE:
			mSimplifyCheckType = CheckType.fromOption(o, value);
			break;
		case OPT_SIMPLIFY_REPEATEDLY:
			mSimplifyRepeatedly = o.checkArg(value, mSimplifyRepeatedly);
			break;
		case OPT_PROOF_CHECK_MODE:
			if ((mProofCheckMode = o.checkArg(value, mProofCheckMode))
				&& mAssertions == null)
				mAssertions = new ScopedArrayList<Term>();
			break;
		default:
			throw new InternalError("This should be implemented!!!");
		}
	}
	
	public Term simplify(Term term) throws SMTLIBException {
		CheckType old = mCheckType;
		int oldNumScopes = mStackLevel;
		try {
			mCheckType = mSimplifyCheckType;
			return new SimplifyDDA(this, mSimplifyRepeatedly).
					getSimplifiedTerm(term);
		} finally {
			mCheckType = old;
			assert (mStackLevel == oldNumScopes);
		}
	}

	/**
	 * Perform a restart and switch the decisions of all undecided literals.
	 * This method should efficiently lead the solver to explore another path
	 * in the search tree. 
	 */
	public void flipDecisions() {
		mEngine.flipDecisions();
	}
	
	/**
	 * Flip the truth value decision for a name literal.
	 * @param name The name used in the annotation for this literal.
	 * @throws SMTLIBException If name not known.
	 */
	public void flipNamedLiteral(String name) throws SMTLIBException {
		mEngine.flipNamedLiteral(name);
	}

	/**
	 * Access to the internal CNF transformer.  Should not be used by users.
	 * @return Internal CNF transformer.
	 */
	public Clausifier getClausifier() {
		return mClausifier;
	}

	/**
	 * Access to the internal DPLL engine.  Should not be used by users.
	 * @return Internal DPLL engine.
	 */
	public DPLLEngine getEngine() {
		return mEngine;
	}	

	/**
	 * Access to the logger used by SMTInterpol.
	 * @return The logger used by SMTInterpol.
	 */
	public Logger getLogger() {
		return mLogger;
	}

	protected void setEngine(DPLLEngine engine) {
		mEngine = engine;
	}

	protected void setClausifier(Clausifier clausifier) {
		mClausifier = clausifier;
	}
	
	private void checkAssertionStackModified() throws SMTLIBException {
		if (mAssertionStackModified)
			throw new SMTLIBException(
					"Assertion stack has been modified since last check-sat!");
	}
	
	private void modifyAssertionStack() {
		mAssertionStackModified = true;
		mModel = null;
	}
	
	private void buildModel() throws SMTLIBException {
		checkAssertionStackModified();
		if (mEngine.inconsistent()) {
			if (mDDFriendly)
				System.exit(4); // NOCHECKSTYLE
			throw new SMTLIBException("Context is inconsistent");
		}
		if (mStatus != LBool.SAT) {
			// Once we have incomplete solvers we might check mReasonUnknown...
			if (mDDFriendly)
				System.exit(9);
			throw new SMTLIBException(
					"Cannot construct model since solving did not complete");
		}
		if (mModel == null) {
			mModel = new
				de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model(
					mClausifier, getTheory(), mPartialModels);
		}
	}
	
	/**
	 * Retrieve the proof in its internal format.  Users should use
	 * {@link #getProof()} to retrieve the proof as a proof term.
	 * @return Internal proof.
	 * @throws SMTLIBException If no proof is present or the proof is found to
	 *                         to be incorrect.
	 */
	@SuppressWarnings("unused")
	public Clause retrieveProof() throws SMTLIBException {
		Clause unsat = mEngine.getProof();
		if (unsat == null) {
			if (mDDFriendly)
				System.exit(5); // NOCHECKSTYLE
			throw new SMTLIBException("Logical context not inconsistent!");
		}
		Clause proof = mProofTransformation.transform(unsat);
		if (Config.CHECK_PROP_PROOF
			&& (proof.getSize() != 0 || !new PropProofChecker().check(proof)))
				throw new SMTLIBException("Proof incorrect");
		return proof;
	}
	
	/**
	 * Get all literals currently set to true.  Note that this function might
	 * also be called if SMTInterpol is currently in an unsat state.  Then, it
	 * will simply return an empty array.
	 * @return All literals currently set to true.
	 * @throws SMTLIBException If the assertion stack is modified since the last
	 *                         clean state.
	 */
	public Term[] getSatisfiedLiterals() throws SMTLIBException {
		checkAssertionStackModified();
		return mEngine.getSatisfiedLiterals();
	}
	
	/**
	 * A helper function to be called from the debugger...
	 */
	@SuppressWarnings("unused")
	private boolean dumpInterpolationBug(
			int[] startOfSubtree, Term[] partition, Term[] ipls, int num) {
		try {
			FileWriter fw = new FileWriter("iplBug.txt");
			FormulaUnLet unlet = new FormulaUnLet();
			PrintTerm outputter = new PrintTerm();
			// Find and assert children
			int child = num - 1;
			while (child >= startOfSubtree[num]) {
				outputter.append(fw, unlet.unlet(ipls[child]));
				child = startOfSubtree[child] - 1;
				fw.append("\nand\n");
			}
			// Assert node
			outputter.append(fw, ((ApplicationTerm) partition[num]).
					getFunction().getDefinition());
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
		} catch (IOException eioe) {
			eioe.printStackTrace();
			return false;
		}
	}
	
	@Override
	public Iterable<Term[]> checkAllsat(final Term[] input) {
		final Literal[] lits = new Literal[input.length];
		for (int i = 0; i < input.length; ++i) {
			if (input[i].getSort() != getTheory().getBooleanSort())
				throw new SMTLIBException("AllSAT over non-Boolean");
			lits[i] = mClausifier.getCreateLiteral(input[i]);
		}
		return new Iterable<Term[]>() {
			
			@Override
			public Iterator<Term[]> iterator() {
				return mEngine.new AllSatIterator(lits, input);
			}
		};
	}
	
	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y)
		throws SMTLIBException, UnsupportedOperationException {
		if (x.length != y.length)
			throw new SMTLIBException("Different number of x's and y's");
		if (x.length < 2)
			throw new SMTLIBException("Need at least two elements to find equality");
		for (int i = 0; i < x.length; ++i)
			if (!x[i].getSort().isNumericSort() 
					|| !y[i].getSort().isNumericSort())
				throw new SMTLIBException("Only numeric types supported");
		LBool isSat = checkSat();
		if (isSat == LBool.UNSAT)
			throw new SMTLIBException("Context is inconsistent!");
		// TODO: If we get unknown, we can nevertheless try.  But quick-check
		//       on numerals won't work since it produces a really dull model
		//       since it does not allow pivoting
//		if (isSat == LBool.UNKNOWN)
//			// We cannot even prove satisfiability of the context.  No chance to
//			// prove inductivity of an equality!
//			return new Term[0];
		Term[] terms = new Term[x.length + y.length];
		System.arraycopy(x, 0, terms, 0, x.length);
		System.arraycopy(y, 0, terms, x.length, y.length);
		Map<Term, Term> vals = getValue(terms);
		Rational x0 = (Rational) ((ConstantTerm) vals.get(x[0])).getValue();
		Rational y0 = (Rational) ((ConstantTerm) vals.get(y[0])).getValue();
		Rational x1 = null, y1 = null;
		for (int i = 1; i < x.length; ++i) {
			x1 = (Rational) ((ConstantTerm) vals.get(x[i])).getValue();
			y1 = (Rational) ((ConstantTerm) vals.get(y[i])).getValue();
			if (x1.equals(x0)) {
				if (!y1.equals(y0))
					// There is no implied equality!
					return new Term[0];
			} else
				break;
		}
		Rational xdiff = x0.sub(x1);
		if (xdiff.equals(Rational.ZERO))
			// There is no implied equality
			return new Term[0];
		Rational a = y0.subdiv(y1, xdiff);
		Rational b = Rational.ONE;
		Rational c = y0.mul(x1).subdiv(x0.mul(y1), xdiff);
		Sort s = x[0].getSort();
		// Check for integers
		if (x[0].getSort().getName().equals("Int")
				&& y[0].getSort().getName().equals("Int")) {
			if (!a.isIntegral()) {
				BigInteger denom = a.denominator();
				a = a.mul(denom);
				b = b.mul(denom);
				c = c.mul(denom);
			}
			if (!c.isIntegral()) {
				BigInteger denom = c.denominator();
				a = a.mul(denom);
				b = b.mul(denom);
				c = c.mul(denom);
			}
		} else if (s.getName().equals("Int"))
			s = sort("Real");
		Term at = a.toTerm(s), bt = b.toTerm(s), ct = c.toTerm(s);
		// Check implication
		if (mCheckType == CheckType.FULL) {
		    // This version only works with full checks.  If we forbid case
		    // splits, we cannot refute the disjunction created by this method.
    		Term[] disj = new Term[x.length];
    		for (int i = 0; i < x.length; ++i)
    			disj[i] = term("not", term("=", term("*", at, x[i]),
    						term("+", term("*", bt, y[i]), ct)));
    		try {
    			push(1);
    			assertTerm(term("or", disj));
    			LBool isImplied = checkSat();
    			if (isImplied != LBool.UNSAT)
    				return new Term[] {};
    		} finally {
    			pop(1);
    		}
		} else { 
        	// This method works for all modes
        	for (int i = 0; i < x.length; ++i) {
        		Term neq = term("not", term("=", term("*", at, x[i]),
        				term("+", term("*", bt, y[i]), ct)));
        		try {
        			push(1);
        			assertTerm(neq);
        			LBool isImplied = checkSat();
        			if (isImplied != LBool.UNSAT)
        				return new Term[] {};
        		} finally {
        			pop(1);
        		}
        	}
		}
		return new Term[] {at, bt, ct};
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
		throws SMTLIBException {
		Sort realSort = resultSort.getRealSort();
		if (realSort.isArraySort()
				&& realSort.getArguments()[0] == getTheory().getBooleanSort())
			throw new UnsupportedOperationException(
					"SMTInterpol does not support Arrays with Boolean indices");
		super.declareFun(fun, paramSorts, resultSort);
	}

	public boolean isTerminationRequested() {
		return mCancel.isTerminationRequested();
	}
}
