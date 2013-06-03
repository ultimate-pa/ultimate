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
import java.util.Timer;
import java.util.TimerTask;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.SimpleLayout;
import org.apache.log4j.WriterAppender;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbolFactory;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.SymbolChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.SymbolCollector;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofTermGenerator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.PropProofChecker;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.Transformations.AvailableTransformations;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.UnsatCoreCollector;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;


public class SMTInterpol extends NoopScript {
	
	private static class SMTInterpolSetup extends Theory.SolverSetup {
		
		private static class RewriteProofFactory extends FunctionSymbolFactory {
			Sort m_ProofSort;
			public RewriteProofFactory(String name, Sort proofSort) {
				super(name);
				m_ProofSort = proofSort;
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
					|| paramSorts[0] != m_ProofSort)
					return null;

				if (paramSorts.length == 2 && paramSorts[0] != paramSorts[1])
					return null;
				
				return paramSorts[0];
			}
		}
		
		private int m_ProofMode;
		
		public SMTInterpolSetup(int proofMode) {
			m_ProofMode = proofMode;
		}

		@Override
		public void setLogic(Theory theory, Logics logic) {
			int leftassoc = FunctionSymbol.LEFTASSOC;
			// Damn Java compiler...
			Sort proof = null;
			Sort[] proof2 = null;
			Sort bool = theory.getSort("Bool");
			Sort[] bool1 = {bool};
			if (m_ProofMode > 0) {
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
			if (m_ProofMode > 1) {
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
			switch (logic) {
			case QF_AUFLIA:
			case AUFLIA:
				declareArraySymbols(theory);
				// Fallthrough
			case QF_UFLIA:
			case QF_LIA:
			case QF_IDL:
			case QF_UFIDL:
			case QF_NIA:
			case UFNIA:
				declareIntSymbols(theory);
				break;
			case AUFLIRA:
			case AUFNIRA:
				declareArraySymbols(theory);
				// Fallthrough
			case QF_UFLIRA:
				declareIntSymbols(theory);
				// Fallthrough to real symbols since mixed logics.
			case LRA:
			case QF_LRA:
			case QF_NRA:
			case QF_UFLRA:
			case QF_UFNRA:
			case QF_RDL:
			case UFLRA:
				declareRealSymbols(theory);
				break;
			default:
				break;
			}
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
		private final String m_OptName;
		private final String m_Description;
		private final boolean m_OnlineModifyable;
		private final int m_OptNum;
		public Option(String optName, String description,
				boolean onlineModifyable, int optnum) {
			m_OptName = optName;
			m_Description = description;
			m_OnlineModifyable = onlineModifyable;
			m_OptNum = optnum;
			SMTInterpol.options.add(this);
		}
		public String getName() {
			return m_OptName;
		}
		public String getDescription() {
			return m_Description;
		}
		public boolean isOnlineModifyable() {
			return m_OnlineModifyable;
		}
		public int getOptionNumber() {
			return m_OptNum;
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
			throw new SMTLIBException("Option " + getName() +
					" expects a Boolean value");
		}
		@SuppressWarnings("unchecked")
		@Override
		public <T> T checkArg(Object value, T curval) throws SMTLIBException {
			if (curval instanceof Boolean)
				return (T) checkArg(value);
			throw new SMTLIBException("Option " + getName() +
				" expects a Boolean value");
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
				} catch (NumberFormatException ignored) {}
			}
			throw new SMTLIBException("Option " + getName() +
					" expects a numeral value");
		}
		@SuppressWarnings("unchecked")
		@Override
		public <T> T checkArg(Object value, T curval) throws SMTLIBException {
			if (curval instanceof BigInteger || curval instanceof Integer ||
					curval instanceof Long)
				return (T) checkArg(value);
			throw new SMTLIBException("Option " + getName() +
				" expects a numeral value");
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
			throw new SMTLIBException("Option " + getName() +
					" expects a string value");
		}
		@SuppressWarnings("unchecked")
		@Override
		public <T> T checkArg(Object value, T curval) throws SMTLIBException {
			if (curval instanceof String)
				return (T) checkArg(value);
			throw new SMTLIBException("Option " + getName() +
				" expects a string value");
		}
	}
	private static class OptionMap {
		private Option[] options;
		private int numOptions;
		public OptionMap() {
			options = new Option[0x10];
			numOptions = 0;
		}
		private void grow() {
			Option[] oldOptions = options;
			options = new Option[options.length * 2];
			for (Option o : oldOptions)
				add_internal(o);
		}
		public void add(Option option) {
			if (++numOptions > options.length)
				grow();
			add_internal(option);
		}
		private void add_internal(Option o) {
			int hash = o.getName().hashCode();
			for (int i = 0; i < options.length; ++i) {
				int idx = (hash + i) & (options.length - 1);
				if (options[idx] == null) {
					options[idx] = o;
					return;
				}
			}
			throw new AssertionError("Did not find empty slot");
		}
		public Option find(String name) {
			int hash = name.hashCode();
			for (int i = 0; i < numOptions; ++i) {
				int idx = (hash + i) & (options.length - 1);
				if (options[idx] == null)
					return null;
				String optname = options[idx].getName();
				if (optname.hashCode() == hash && optname.equals(name))
					return options[idx];
			}
			return null;
		}
		public String[] getOptionNames() {
			String[] res = new String[numOptions];
			int pos = 0;
			for (Option o : options) {
				if (o != null) {
					res[pos] = o.getName();
					if (++pos == numOptions)
						return res;
				}
			}
			// Should never be reached
			return res;
		}
	}
	private DPLLEngine m_Engine;
	private Clausifier m_Clausifier;
	private ScopedArrayList<Term> m_Assertions;
	
	private String m_OutName = "stdout";
	private PrintWriter m_Err = new PrintWriter(System.err);
	private String m_ErrName = "stderr";
	private SimpleLayout m_Layout;
	private Logger m_Logger;
	private WriterAppender m_Appender;
	
	String m_ErrorMessage;
	boolean m_ProduceModels = false;
	long m_RandomSeed = Config.RANDOM_SEED;
	boolean m_ProduceProofs = false;
	boolean m_ProduceUnsatCores = false;
	boolean m_ProduceAssignment = false;
	boolean m_ProduceInterpolants = false;
	/**
	 * Current state of the option :print-success. If this is false,
	 * the success output of the commands are not printed.
	 */
	boolean m_ReportSuccess = true;
	/**
	 * Current state of the option :print-terms-cse.  If this is 
	 * true common subexpressions in output are eliminated by lets.
	 */
	boolean m_PrintCSE = true;
	
	boolean m_InterpolantCheckMode = false;
	boolean m_UnsatCoreCheckMode = false;
	boolean m_ModelCheckMode = false;
	
	private int m_ProofMode;
	
	de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model m_Model = null;
	private boolean m_PartialModels = false;
	
	private final static Object NAME = new QuotedObject("SMTInterpol");
	private final static Object VERSION = new QuotedObject("2.0");
	private final static Object AUTHORS = new QuotedObject(
					"Jochen Hoenicke, Juergen Christ, and Alexander Nutz");
	private final static Object INTERPOLATION_METHOD = new QuotedObject("tree");
	// I assume an initial check s.t. first (get-info :status) returns sat
	private LBool m_Status = LBool.SAT;
	
	// The status set in the benchmark
	private String m_StatusSet = null;
	private ReasonUnknown m_ReasonUnknown = null;
	// Soft timeout for the solver (in milliseconds)
	private long m_Timeout;
	
	// The assertion stack was modified after the last check-sat, i.e., the
	// m_status field is not valid and we have to deactivate
	// get-{value,model,interpolants,proof}.
	private boolean m_AssertionStackModified = true;
	// The assertion stack level at which the first division-by-0 was
	// encountered.  If it is -1, it means "never"
	private int m_By0Seen = -1;
	
	// The proof transformation currently used.
	private AvailableTransformations m_ProofTransformation =
		AvailableTransformations.NONE;
	
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
	//// Add a new option number for every new option
	
	// The Options Map
	private final static OptionMap options = new OptionMap();
	
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
		//// Create new option object for every new option
	}
	
	public SMTInterpol() {
		this(Logger.getRootLogger(), true);
	}
	
	public SMTInterpol(Logger logger) {
		this(logger, false);
	}
	
	public SMTInterpol(Logger logger, boolean ownLogger) {
		m_Logger = logger;
		if (ownLogger) {
			m_Layout = new SimpleLayout();
			m_Appender = new WriterAppender(m_Layout, m_Err);
	        m_Logger.addAppender(m_Appender);
	        m_Logger.setLevel(Config.DEFAULT_LOG_LEVEL);
		}
        m_Timeout = 0;
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
	private SMTInterpol(SMTInterpol other, Map<String, Object> options) {
		super(other.getTheory());
		m_Logger = other.m_Logger;
		m_Timeout = other.m_Timeout;
		if (options != null)
			for (Map.Entry<String, Object> me : options.entrySet())
				setOption(me.getKey(), me.getValue());
		m_Engine = new DPLLEngine(getTheory(), m_Logger);
        m_Clausifier = new Clausifier(m_Engine, 0);
		m_Clausifier.setLogic(getTheory().getLogic());
		m_Engine.getRandom().setSeed(m_RandomSeed);
	}
	
	public void reset() {
		super.reset();
		m_Engine = null;
		m_Model = null;
		m_AssertionStackModified = true;
        if (m_Assertions != null)
        	m_Assertions.clear();
	}
	
	public void push(int n) throws SMTLIBException {
		super.push(n);
		modifyAssertionStack();
		while (n-- > 0) {
			if (m_Assertions != null)
				m_Assertions.beginScope();
			m_Clausifier.push();
		}
	}
	
	public void pop(int n) throws SMTLIBException {
		super.pop(n);
		modifyAssertionStack();
		int i = n;
		while (i-- > 0) {
			if (m_Assertions != null)
				m_Assertions.endScope();
		}
		m_Clausifier.pop(n);
		if (m_StackLevel < m_By0Seen)
			// We've popped all division-by-0s.
			m_By0Seen = -1;
	}
		
	public LBool checkSat() throws SMTLIBException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		m_Model = null;
		m_AssertionStackModified = false;
		Timer timer = null;
		if (m_Timeout > 0) {
			timer = new Timer("Timing thread",true);
			timer.schedule(new TimerTask() {

				@Override
				public void run() {
					synchronized (m_Engine) {
						m_Engine.setCompleteness(DPLLEngine.INCOMPLETE_TIMEOUT);
						m_Engine.stop();
					}
				}
			
			}, m_Timeout);
		}
		
		LBool result = LBool.UNKNOWN;
		m_ReasonUnknown = ReasonUnknown.INCOMPLETE;
		m_Engine.setRandomSeed(m_RandomSeed);
		try {
			if (m_Engine.solve()) {
				if (m_Engine.hasModel()) {
					result = LBool.SAT;
					if (m_ModelCheckMode/* && m_ProduceModels*/) {
						// Damn coding conventions!  There is no way to format
						// this nicely!!!
						m_Model = new de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model(
								m_Clausifier, getTheory(), m_PartialModels);
						for (Term asserted : m_Assertions) {
							Term checkedResult = m_Model.evaluate(asserted);
							if (checkedResult != getTheory().TRUE)
								m_Logger.fatal("Model does not satisfy " + 
										asserted.toStringDirect());
						}
					}
				} else {
					result = LBool.UNKNOWN;
					switch(m_Engine.getCompleteness()) {
					case DPLLEngine.COMPLETE:
						throw new InternalError("Complete but no model?");
					case DPLLEngine.INCOMPLETE_MEMOUT:
						m_ReasonUnknown = ReasonUnknown.MEMOUT;
						break;
					case DPLLEngine.INCOMPLETE_TIMEOUT:
						m_ReasonUnknown = ReasonUnknown.TIMEOUT;
						break;
					case DPLLEngine.INCOMPLETE_QUANTIFIER:
					case DPLLEngine.INCOMPLETE_THEORY:
						m_ReasonUnknown = ReasonUnknown.INCOMPLETE;
						break;
					case DPLLEngine.INCOMPLETE_UNKNOWN:
						m_ReasonUnknown = ReasonUnknown.CRASHED;
						break;
					default:
						throw new InternalError("Unknown incompleteness reason");
					}
					m_Logger.info(
							new DebugMessage(
									"Got {0} as reason to return unknown",
									m_Engine.getCompletenessReason()));
				}
			} else {
				result = LBool.UNSAT;
			}
		} catch (OutOfMemoryError oom) {
			// BUGFIX: Don't do this since log4j will produce another OOM.
//			m_Logger.fatal("OOM during check ",oom);
			m_ReasonUnknown = ReasonUnknown.MEMOUT;
		} catch (Throwable ex) {
			m_Logger.fatal("Error during check ",ex);
			m_ReasonUnknown = ReasonUnknown.CRASHED;
		}
		m_Status = result;
		if (Config.CHECK_STATUS_SET) {
			if (isStatusSet() && m_ReasonUnknown != ReasonUnknown.MEMOUT &&
					!m_Status.toString().equals(m_StatusSet)) {
				m_Logger.warn("Status differs: User said " + m_StatusSet +
						" but we got " + m_Status);
			}
		}
		m_StatusSet = null;
		if (timer != null)
			timer.cancel();
		return result;
	}
	
	private final boolean isStatusSet() {
		return m_StatusSet != null && !m_StatusSet.equals("unknown");
	}

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
	
	public void setLogic(Logics logic)
	throws UnsupportedOperationException, SMTLIBException {
		m_SolverSetup = new SMTInterpolSetup(m_ProofMode);
		super.setLogic(logic);
		try {
			m_Engine = new DPLLEngine(getTheory(), m_Logger);
	        m_Clausifier = new Clausifier(m_Engine, m_ProofMode);
	        // This has to be before set-logic since we need to capture
	        // initialization of CClosure.
	        m_Engine.setProofGeneration(
					m_ProduceProofs || m_ProduceUnsatCores || m_ProduceInterpolants);
			m_Clausifier.setLogic(logic);
			m_Clausifier.setAssignmentProduction(m_ProduceAssignment);
			m_Engine.setProduceAssignments(m_ProduceAssignment);
			m_Engine.setRandomSeed(m_RandomSeed);
		} catch (UnsupportedOperationException logicUnsupported) {
			super.reset();
			m_Engine = null;
			m_Clausifier = null;
			throw logicUnsupported;
		}
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		super.assertTerm(term);
		if (!term.getSort().equals(getTheory().getBooleanSort())) {
			if (term.getSort().getTheory() != getTheory())
				throw new SMTLIBException("Asserted terms created with incompatible theory");
			else
				throw new SMTLIBException("Asserted terms must have sort Bool");
		}
		if (Config.STRONG_USAGE_CHECKS && term.getFreeVars().length != 0)
			throw new SMTLIBException("Asserted terms must be closed");
		if (m_Assertions != null)
			m_Assertions.add(term);
		if (m_Engine.inconsistent()) {
			m_Logger.info("Asserting into inconsistent context");
			return LBool.UNSAT;
		}
		try {
			modifyAssertionStack();
			m_Clausifier.addFormula(term);
			/* We always have to reset the flag, but only need to set the stack
			 * level if it is not already set. 
			 */
			if (m_Clausifier.resetBy0Seen() && m_By0Seen == -1)
				m_By0Seen = m_StackLevel;
			if (!m_Engine.quickCheck()) {
				m_Logger.info("Assertion made context inconsistent");
				return LBool.UNSAT;
			}
		} catch (UnsupportedOperationException ex) {
			throw new SMTLIBException(ex.getMessage());
		}
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		if (m_Assertions != null)
			return m_Assertions.toArray(new Term[m_Assertions.size()]);
		throw new SMTLIBException(
				"Set option :interactive-mode to true to get assertions!");
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		if (!m_Engine.isProduceAssignments())
			throw new SMTLIBException(
				"Set option :produce-assignments to true to generate assignments!");
		checkAssertionStackModified();
		return m_Engine.getAssignments();
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		if (":status".equals(info))
			return m_Status;
		if (":name".equals(info))
			return NAME;
		if (":version".equals(info))
			return VERSION;
		if (":authors".equals(info))
			return AUTHORS;
		if (":all-statistics".equals(info)) {
			return m_Engine == null ? new Object[0] : m_Engine.getStatistics();
		}
		if (":status-set".equals(info))
			return m_StatusSet;
		if (":options".equals(info)) {
			return options.getOptionNames();
		}
		if (":reason-unknown".equals(info)) {
			if (m_Status != LBool.UNKNOWN)
				throw new SMTLIBException("Status not unknown");
			return m_ReasonUnknown;
		}
		if (":assertion-stack-levels".equals(info))
			return m_StackLevel;
		// Info from our SMTLIB interpolation proposal
		if (":interpolation-method".equals(info))
			return INTERPOLATION_METHOD;
		Option opt = options.find(info);
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
		Option o = options.find(opt);
		if (o == null)
			throw new UnsupportedOperationException();
		switch (o.getOptionNumber()) {
		case OPT_PRINT_SUCCESS:
			return m_ReportSuccess;
		case OPT_VERBOSITY:
			switch(m_Logger.getLevel().toInt()) {
			case Level.ALL_INT:
				return BigInteger.valueOf(6);
			case Level.DEBUG_INT:
				return BigInteger.valueOf(5);
			case Level.INFO_INT:
				return BigInteger.valueOf(4);
			case Level.WARN_INT:
				return BigInteger.valueOf(3);
			case Level.ERROR_INT:
				return BigInteger.valueOf(2);
			case Level.FATAL_INT:
				return BigInteger.valueOf(1);
			default:
				return BigInteger.valueOf(0);
			}
		case OPT_TIMEOUT:
			return BigInteger.valueOf(m_Timeout);
		case OPT_REGULAR_OUTPUT_CHANNEL:
			return m_OutName;
		case OPT_DIAGNOSTIC_OUTPUT_CHANNEL:
			return m_ErrName;
		case OPT_PRODUCE_PROOFS:
			return m_ProduceProofs;
		case OPT_PRODUCE_MODELS:
			return m_ProduceModels;
		case OPT_PRODUCE_ASSIGNMENTS:
			return m_ProduceAssignment;
		case OPT_RANDOM_SEED:
			return BigInteger.valueOf(m_RandomSeed);
		case OPT_INTERACTIVE_MODE:
			return m_Assertions != null;
		case OPT_INTERPOLANT_CHECK_MODE:
			return m_InterpolantCheckMode;
		case OPT_PRODUCE_UNSAT_CORES:
			return m_ProduceUnsatCores;
		case OPT_UNSAT_CORE_CHECK_MODE:
			return m_UnsatCoreCheckMode;
		case OPT_PRINT_TERMS_CSE:
			return m_PrintCSE;
		case OPT_MODEL_CHECK_MODE:
			return m_ModelCheckMode;
		case OPT_PROOF_TRANSFORMATION:
			return m_ProofTransformation.name();
		case OPT_PRODUCE_INTERPOLANTS:
			return m_ProduceInterpolants;
		case OPT_MODELS_PARTIAL:
			return m_PartialModels;
		default:
			throw new InternalError("This should be implemented!!!");
		}
	}

	@Override
	public Term getProof()
	throws SMTLIBException, UnsupportedOperationException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		int proofMode = 0;
		if (m_ProduceInterpolants || m_ProduceUnsatCores)
			proofMode = 1;
		if (m_ProduceProofs)
			proofMode = 2;
		if (proofMode == 0)
			throw new SMTLIBException("Option :produce-proofs not set to true");
		if (proofMode == 1)
			m_Logger.warn("Using partial proofs (cut at CNF-level).  " +
					"Set option :produce-proofs to true to get complete proofs."
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
			if (m_By0Seen != -1)
				res = new Div0Remover().transform(res);
			return res;
		} catch (Exception exc) {	
			throw new SMTLIBException(exc.getMessage() == null ? 
					exc.toString() : exc.getMessage());
		}
	}
	
	@SuppressWarnings("unchecked")
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree) {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		if (!m_ProduceProofs && !m_ProduceInterpolants)
			throw new SMTLIBException(
					"Interpolant production not enabled.  Set either :produce-interpolants or :produce-proofs to true");
		checkAssertionStackModified();
		Clause refutation = retrieveProof();
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
					j = startOfSubtree[j-1];
				if (startOfSubtree[i] != j)
					throw new SMTLIBException("malformed subtree array.");
			}
			if (startOfSubtree[partition.length-1] != 0)
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
			if (!fsym.isIntern()) {
				terms = new Term[] { partition[i] };
			} else {
				if (!fsym.getName().equals("and"))
					throw new SMTLIBException(errormsg);
				terms = ((ApplicationTerm) partition[i]).getParameters();
			}
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
		if (m_InterpolantCheckMode) {
			HashSet<String> usedParts = new HashSet<String>();
			for (Set<String> part : parts)
				usedParts.addAll(part);
			tmpBench = new SMTInterpol(this,
					Collections.singletonMap(":interactive-mode",
							(Object)Boolean.TRUE));
			Level old = tmpBench.m_Logger.getLevel();
			try {
				tmpBench.m_Logger.setLevel(Level.ERROR);
				// Clone the current context except for the parts used in the
				// interpolation problem
				collector = new SymbolCollector();
				collector.startCollectTheory();
				termloop: for (Term asserted : m_Assertions) {
					if (asserted instanceof AnnotatedTerm) {
						AnnotatedTerm annot = (AnnotatedTerm) asserted;
						for (Annotation an : annot.getAnnotations()) {
							if (":named".equals(an.getKey()) && 
									usedParts.contains(an.getValue()))
								continue termloop;
						}
					}
					tmpBench.assertTerm(asserted);
					collector.addGlobalSymbols(asserted);
				}
				globals = collector.getTheorySymbols();
			} finally {
				tmpBench.m_Logger.setLevel(old);
			}
			// free space
			usedParts = null;
		}
		Interpolator interpolator =
			new Interpolator(m_Logger, tmpBench, getTheory(), parts, startOfSubtree);
		Term[] ipls = interpolator.getInterpolants(refutation);
		
		if (m_By0Seen != -1) {
			Div0Remover rem = new Div0Remover();
			for (int i = 0; i < ipls.length; ++i)
				ipls[i] = rem.transform(ipls[i]);
		}
		
		if (m_InterpolantCheckMode) {
			boolean error = false;
			Level old = tmpBench.m_Logger.getLevel();
			try {
				tmpBench.m_Logger.setLevel(Level.ERROR);
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
						for (Map.Entry<FunctionSymbol, Integer> me :
							occs[child].entrySet()) {
							Integer ival = occs[i].get(me.getKey());
							ival = ival == null ? me.getValue() :
								ival + me.getValue();
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
						m_Logger.error("Could not assert interpolant", exc);
					}
					LBool res = tmpBench.checkSat();
					if (res != LBool.UNSAT) {
						m_Logger.error(new DebugMessage(
								"Interpolant {0} not inductive: " +
								" (Check returned {1})", i, res));
						error = true;
					}
					tmpBench.pop(1);
					// Check symbol condition
					if (i != ipls.length) {
						if (checker.check(ipls[i], occs[i], occs[ipls.length])) {
							m_Logger.error(new DebugMessage(
									"Symbol error in Interpolant {0}.  " +
									"Subtree only symbols: {1}.  " +
									"Non-subtree only symbols: {2}.", i,
									checker.getLeftErrors(),
									checker.getRightErrors()));
							error = true;
						}
					}
				}
			} finally {
				tmpBench.m_Logger.setLevel(old);
				// Not needed for now, but maybe later...
				tmpBench.exit();
			}
			if (error)
				throw new SMTLIBException
					("generated interpolants did not pass sanity check");
		}
		return ipls;
	}
	
	@Override
	public Term[] getUnsatCore()
	throws SMTLIBException, UnsupportedOperationException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		if (!m_ProduceUnsatCores)
			throw new SMTLIBException(
					"Set option :produce-unsat-cores to true before using get-unsat-cores");
		checkAssertionStackModified();
		UnsatCoreCollector ucc = new UnsatCoreCollector(this);
		Clause unsat = m_Engine.getProof();
		if (unsat == null)
			throw new SMTLIBException("Logical context not inconsistent!");
		Term[] core = ucc.getUnsatCore(unsat);
		if (m_UnsatCoreCheckMode) {
			HashSet<String> usedParts = new HashSet<String>();
			for (Term t : core)
				usedParts.add(((ApplicationTerm)t).getFunction().getName());
			SMTInterpol tmpBench = new SMTInterpol(this, null);
			Level old = tmpBench.m_Logger.getLevel();
			try {
				tmpBench.m_Logger.setLevel(Level.ERROR);
				// Clone the current context except for the parts used in
				// the unsat core
				termloop: for (Term asserted : m_Assertions) {
					if (asserted instanceof AnnotatedTerm) {
						AnnotatedTerm annot = (AnnotatedTerm) asserted;
						for (Annotation an : annot.getAnnotations()) {
							if (":named".equals(an.getKey()) && 
									usedParts.contains(an.getValue()))
								continue termloop;
						}
					}
					tmpBench.assertTerm(asserted);
				}
				for (Term t : core)
					tmpBench.assertTerm(t);
				LBool isUnsat = tmpBench.checkSat();
				if (isUnsat != LBool.UNSAT) {
					m_Logger.error(new DebugMessage(
							"Unsat core could not be proven unsat (Result is {0})",
							isUnsat));
				}
			} finally {
				tmpBench.m_Logger.setLevel(old);
				// Not needed for now, but maybe later...
				tmpBench.exit();
			}
		}
		return core;
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms)
	throws SMTLIBException, UnsupportedOperationException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		buildModel();
		return m_Model.evaluate(terms);
	}
	
	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		if (m_Engine == null)
			throw new SMTLIBException("No logic set!");
		buildModel();
		return m_Model;
	}

	@Override
	public void setInfo(String info, Object value) {
		if (info.equals(":status")
			&& value instanceof String) {
			if (value.equals("sat")) {
				m_Status = LBool.SAT;
				m_StatusSet = "sat";
			} else if (value.equals("unsat")) {
				m_Status = LBool.UNSAT;
				m_StatusSet = "unsat";
			} else if (value.equals("unknown")) {
				m_Status = LBool.UNKNOWN;
				m_StatusSet = "unknown";
			}
		}
	}
	
	public PrintWriter createChannel(String file) throws IOException {
		if (file.equals("stdout"))
			return new PrintWriter(System.out);
		else if (file.equals("stderr"))
			return new PrintWriter(System.err);
		else
			return new PrintWriter(new FileWriter(file));
	}
	
	private final void checkOnlineModifyable(Option opt) throws SMTLIBException {
		if (m_Engine != null && !opt.isOnlineModifyable())
			throw new SMTLIBException("Option " + opt.getName() + 
					" can only be changed before setting the logic");
	}
	
	@Override
	public void setOption(String opt, Object value)
	throws UnsupportedOperationException, SMTLIBException {
		Option o = options.find(opt);
		if (o == null)
			throw new UnsupportedOperationException();
		checkOnlineModifyable(o);
		switch (o.getOptionNumber()) {
		case OPT_PRINT_SUCCESS:
			m_ReportSuccess = o.checkArg(value, m_ReportSuccess);
			break;
		case OPT_VERBOSITY:
			BigInteger blevel = o.checkArg(value, BigInteger.ZERO);// FAKE...
			int level = blevel.bitLength() >= 32 ? 
					Integer.MAX_VALUE : blevel.intValue();
			if (level > 5)
				m_Logger.setLevel(Level.ALL);
			else if (level > 4)
				m_Logger.setLevel(Level.DEBUG);
			else if (level > 3)
				m_Logger.setLevel(Level.INFO);
			else if (level > 2)
				m_Logger.setLevel(Level.WARN);
			else if (level > 1)
				m_Logger.setLevel(Level.ERROR);
			else if (level > 0)
				m_Logger.setLevel(Level.FATAL);
			else if (level == -1)
				m_Logger.setLevel(Level.TRACE);
			else
				m_Logger.setLevel(Level.OFF);
			break;
		case OPT_TIMEOUT:
		{
			BigInteger val = o.checkArg(value, BigInteger.ZERO);// FAKE...
			if (val.signum() == -1)
				m_Timeout = 0;
			else if (val.bitLength() < 63)
				m_Timeout = val.longValue();
			else
				// Don't think anyone will wait for that time...
				m_Timeout = Long.MAX_VALUE;
			break;
		}
		case OPT_REGULAR_OUTPUT_CHANNEL:
			m_OutName = o.checkArg(value, m_OutName);
			break;
		case OPT_DIAGNOSTIC_OUTPUT_CHANNEL:
			if (m_Appender == null)
				throw new SMTLIBException("SMTInterpol does not own the logger");
			try {
				String arg = o.checkArg(value, m_ErrName);
				m_Err = createChannel(arg);
				m_Appender.setWriter(m_Err);
				m_ErrName = arg;
			} catch (IOException ex) {
				m_Logger.error(ex);
				throw new SMTLIBException("file not found: "+value);
			}
			break;
		case OPT_PRODUCE_PROOFS:
			if (m_ProduceProofs = o.checkArg(value, m_ProduceProofs))
				m_ProofMode = 2;
			break;
		case OPT_PRODUCE_MODELS:
			m_ProduceModels = o.checkArg(value, m_ProduceModels);
			break;
		case OPT_PRODUCE_ASSIGNMENTS:
			if (m_ProduceAssignment = o.checkArg(value, m_ProduceAssignment)
				&& m_ProofMode == 0)
				m_ProofMode = 1;
			break;
		case OPT_RANDOM_SEED:
		{
			BigInteger val = o.checkArg(value, BigInteger.ZERO);//FAKE...
			m_RandomSeed = val.bitLength() < 64 ? 
					val.longValue() : Long.MAX_VALUE;
			if (m_Engine != null)
				m_Engine.setRandomSeed(m_RandomSeed);
			break;
		}
		case OPT_INTERACTIVE_MODE:
			if (o.checkArg(value, Boolean.TRUE) == Boolean.TRUE)// FAKE...
				m_Assertions = new ScopedArrayList<Term>();
			else if (!m_InterpolantCheckMode && !m_UnsatCoreCheckMode)
				m_Assertions = null;
			break;
		case OPT_INTERPOLANT_CHECK_MODE:
			if (m_InterpolantCheckMode =
				o.checkArg(value, m_InterpolantCheckMode))
				if (m_Assertions == null)
					m_Assertions = new ScopedArrayList<Term>();
			break;
		case OPT_PRODUCE_UNSAT_CORES:
			if (m_ProduceUnsatCores = o.checkArg(value, m_ProduceUnsatCores) &&
				m_ProofMode == 0)
				m_ProofMode = 1;
			break;
		case OPT_UNSAT_CORE_CHECK_MODE:
			if (m_UnsatCoreCheckMode = o.checkArg(value, m_UnsatCoreCheckMode))
				if (m_Assertions == null)
					m_Assertions = new ScopedArrayList<Term>();
			break;
		case OPT_PRINT_TERMS_CSE:
			m_PrintCSE = o.checkArg(value, m_PrintCSE);
			break;
		case OPT_MODEL_CHECK_MODE:
			if (m_ModelCheckMode = o.checkArg(value, m_ModelCheckMode))
				if (m_Assertions == null)
					m_Assertions = new ScopedArrayList<Term>();
			break;
		case OPT_PROOF_TRANSFORMATION: {
			String arg = o.checkArg(value, ""); // FAKE dummy
			try {
				AvailableTransformations tmp =
					AvailableTransformations.valueOf(arg);
				m_ProofTransformation = tmp;
			} catch (IllegalArgumentException iae) {
				// The enum constant is not present
				StringBuilder sb = new StringBuilder();
				sb.append("Illegal value. Only ");
				String sep = "";
				for (AvailableTransformations a :
					AvailableTransformations.values()) {
					sb.append(sep).append(a.name());
					sep = ", ";
				}
				sb.append(" allowed.");
				throw new SMTLIBException(sb.toString());
			}
			break;
		}
		case OPT_PRODUCE_INTERPOLANTS:
			if (m_ProduceInterpolants = o.checkArg(value, m_ProduceInterpolants)
				&& m_ProofMode == 0)
				m_ProofMode = 1;
			break;
		case OPT_MODELS_PARTIAL:
			m_PartialModels = o.checkArg(value, m_PartialModels);
			m_Model = null;
			break;
		default:
			throw new InternalError("This should be implemented!!!");
		}
	}
	
	public Term simplifyTerm(Term term) throws SMTLIBException {
		SimplifyDDA simplifyDDA = new SimplifyDDA(this, this.getLogger());
		Term simp = simplifyDDA.getSimplifiedTerm(term);
		return simp;
		
//		if (m_Engine == null)
//			throw new SMTLIBException("No logic set!");
//		return m_Converter.simplify(term);
//		throw new UnsupportedOperationException();
	}

	/**
	 * Perform a restart and switch the decisions of all undecided literals.
	 * This method should efficiently lead the solver to explore another path
	 * in the search tree. 
	 */
	public void flipDecisions() {
		m_Engine.flipDecisions();
	}
	
	/**
	 * Flip the truth value decision for a name literal.
	 * @param name The name used in the annotation for this literal.
	 * @throws SMTLIBException If name not known.
	 */
	public void flipNamedLiteral(String name) throws SMTLIBException {
		m_Engine.flipNamedLiteral(name);
	}

	public Clausifier getClausifier() {
		return m_Clausifier;
	}

	public DPLLEngine getEngine() {
		return m_Engine;
	}	

	public Logger getLogger() {
		return m_Logger;
	}	

	protected void setEngine(DPLLEngine engine) {
		m_Engine = engine;
	}

	protected void setClausifier(Clausifier clausifier) {
		m_Clausifier = clausifier;
	}
	
	private void checkAssertionStackModified() throws SMTLIBException {
		if (m_AssertionStackModified)
			throw new SMTLIBException(
					"Assertion stack has been modified since last check-sat!");
	}
	
	private void modifyAssertionStack() {
		m_AssertionStackModified = true;
		m_Model = null;
	}
	
	private void buildModel() throws SMTLIBException {
		checkAssertionStackModified();
		if (m_Engine.inconsistent())
			throw new SMTLIBException("Context is inconsistent");
		if (m_Model == null) {
			m_Model = new
				de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model(
					m_Clausifier, getTheory(), m_PartialModels);
		}
	}
	
	public Clause retrieveProof() throws SMTLIBException {
		Clause unsat = m_Engine.getProof();
		if (unsat == null)
			throw new SMTLIBException("Logical context not inconsistent!");
		Clause proof = m_ProofTransformation.transform(unsat);
		if (Config.CHECK_PROP_PROOF) {
			if (proof.getSize() != 0 || !new PropProofChecker().check(proof))
				throw new SMTLIBException("Proof incorrect");
		}
		return proof;
	}
	
	public Term[] getSatisfiedLiterals() throws SMTLIBException {
		checkAssertionStackModified();
		return m_Engine.getSatisfiedLiterals();
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
		} catch (IOException ioe) {
			ioe.printStackTrace();
			return false;
		}
	}
	
	public Iterable<Term[]> checkAllsat(final Term[] input) {
		final Literal[] lits = new Literal[input.length];
		for (int i = 0; i < input.length; ++i) {
			if (input[i].getSort() != getTheory().getBooleanSort())
				throw new SMTLIBException("AllSAT over non-Boolean");
			lits[i] = m_Clausifier.getCreateLiteral(input[i]);
		}
		return new Iterable<Term[]>() {
			
			@Override
			public Iterator<Term[]> iterator() {
				return m_Engine.new AllSatIterator(lits, input);
			}
		};
	}

}
