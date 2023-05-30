/*
 * Copyright (C) 2020 Vincent Langenfeld <langenfv@tf.uni-freiburg.de>
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;


import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseBits;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator.InvariantInfeasibleException;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences;
import de.uni_freiburg.informatik.ultimate.pea2boogie.results.ReqCheck;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.CheckedReqLocation;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

/**
 *
 * @author Vincent Langenfeld <langenfv@tf.uni-freiburg.de>
 *
 */
public class ReqCheckAnnotator implements IReq2PeaAnnotator {

	private static final boolean DEBUG_ONLY_FIRST_NON_TRIVIAL_RT_INCONSISTENCY = false;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final PeaResultUtil mPeaResultUtil;
	private final BoogieLocation mUnitLocation;

	private boolean mCheckVacuity;
	private int mCombinationNum;
	private boolean mCheckConsistency;
	private boolean mCheckComplement;
	private boolean mReportTrivialConsistency;

	private boolean mSeparateInvariantHandling;
	private RtInconcistencyConditionGenerator mRtInconcistencyConditionGenerator;
	private final NormalFormTransformer<Expression> mNormalFormTransformer;
	private final IReqSymbolTable mSymbolTable;
	private final List<ReqPeas> mReqPeas;

	private final Durations mDurations;

	public ReqCheckAnnotator(final IUltimateServiceProvider services, final ILogger logger, final List<ReqPeas> reqPeas,
			final IReqSymbolTable symbolTable, final Durations durations) {
		mLogger = logger;
		mServices = services;
		mSymbolTable = symbolTable;
		mReqPeas = reqPeas;
		mPeaResultUtil = new PeaResultUtil(mLogger, mServices);
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		mUnitLocation = new BoogieLocation("", -1, -1, -1, -1);
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		mDurations = durations;

	}

	@Override
	public List<Statement> getStateChecks() {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		// set preferences
		mCheckVacuity = prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_VACUITY);

		if (prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_RT_INCONSISTENCY)) {
			final int length = mReqPeas.size();
			mCombinationNum = Math.min(length, prefs.getInt(Pea2BoogiePreferences.LABEL_RT_INCONSISTENCY_RANGE));
		} else {
			mCombinationNum = -1;
		}
		mCheckConsistency = prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_CONSISTENCY);
		mReportTrivialConsistency = prefs.getBoolean(Pea2BoogiePreferences.LABEL_REPORT_TRIVIAL_RT_CONSISTENCY);
		mSeparateInvariantHandling = prefs.getBoolean(Pea2BoogiePreferences.LABEL_RT_INCONSISTENCY_USE_ALL_INVARIANTS);
		mCheckComplement = prefs.getBoolean(Pea2BoogiePreferences.LABEL_CHECK_COMPLEMENT);

		// log preferences
		mLogger.info(String.format("%s=%s, %s=%s, %s=%s, %s=%s, %s=%s, %s=%s", Pea2BoogiePreferences.LABEL_CHECK_VACUITY,
				mCheckVacuity, Pea2BoogiePreferences.LABEL_RT_INCONSISTENCY_RANGE, mCombinationNum,
				Pea2BoogiePreferences.LABEL_CHECK_CONSISTENCY, mCheckConsistency,
				Pea2BoogiePreferences.LABEL_REPORT_TRIVIAL_RT_CONSISTENCY, mReportTrivialConsistency,
				Pea2BoogiePreferences.LABEL_RT_INCONSISTENCY_USE_ALL_INVARIANTS, mSeparateInvariantHandling,
				Pea2BoogiePreferences.LABEL_CHECK_COMPLEMENT, mCheckComplement));

		final List<Declaration> decls = new ArrayList<>();
		decls.addAll(mSymbolTable.getDeclarations());

		RtInconcistencyConditionGenerator rticGenerator;
		try {
			if (mCombinationNum >= 1) {
				final BoogieDeclarations boogieDeclarations = new BoogieDeclarations(decls, mLogger);
				rticGenerator = new RtInconcistencyConditionGenerator(mLogger, mServices, mPeaResultUtil, mSymbolTable,
						mReqPeas, boogieDeclarations, mDurations, mSeparateInvariantHandling);
			} else {
				rticGenerator = null;
			}
		} catch (final InvariantInfeasibleException e) {
			mPeaResultUtil.infeasibleInvariant(e);
			mRtInconcistencyConditionGenerator = null;
			return Collections.emptyList();
		}
		mRtInconcistencyConditionGenerator = rticGenerator;
		return generateAnnotations();
	}

	private List<Statement> generateAnnotations() {
		final List<Statement> annotations = new ArrayList<>();
		if (mCheckConsistency) {
			annotations.addAll(genCheckConsistency(mUnitLocation));
		}
		if (mCheckVacuity) {
			annotations.addAll(genChecksNonVacuity(mUnitLocation));
		}
		if (mCheckComplement) {
			annotations.addAll(genCheckComplement(mUnitLocation));
		}
		annotations.addAll(genChecksRTInconsistency(mUnitLocation));
		return annotations;
	}

	private static List<Statement> genCheckConsistency(final BoogieLocation bl) {
		final ReqCheck check = new ReqCheck(Spec.CONSISTENCY);
		final Expression expr = ExpressionFactory.createBooleanLiteral(bl, false);
		return Collections.singletonList(createAssert(expr, check, "CONSISTENCY"));
	}
	

	private List<Statement> genCheckComplement(final BoogieLocation bl) {
		final List<Statement> stmtList = new ArrayList<>();
		ReqPeas reqPeaTotal = mReqPeas.get(0);
		ReqPeas reqPeaComplement = mReqPeas.get(1);
		// List<Entry<CounterTrace, PhaseEventAutomata>> peas = reqPea.getCounterTrace2Pea();
		// we can only check for complement if we have exactly two PEAs
		PhaseEventAutomata a0 = reqPeaTotal.getCounterTrace2Pea().get(0).getValue();
		PhaseEventAutomata a1 = reqPeaComplement.getCounterTrace2Pea().get(0).getValue();
		final Statement assertComplement = genAssertComplement(a0, a1, bl);
		if (assertComplement != null) {
			stmtList.add(assertComplement);
		}
		return stmtList;
	}
	
	/**
	 * Generate the assertion that is violated if the TWO given automata are NOT complements of each other. The
	 * assertion expresses that the automata will never accept or reject the same words if one is the complement automaton of the other, 
	 * i.e. pea 1 can not be in a terminal state if pea 2 is, and pea 1 can not be in a non-terminal state if pea 2 is. 
	 * If this is the case, they have a word "in common" and are NOT complements of each other.
	 *
	 * @param peas
	 *            List of peas, should contain only two elements
	 * @param bl
	 *            A boogie location used for all statements.
	 * @return The assertion for non-complementness
	 */
	private Statement genAssertComplement(PhaseEventAutomata a0, PhaseEventAutomata a1, final BoogieLocation bl) {
		final Pair<List<Expression>, List<Expression>> expressionsA0 = getExpressions(a0, bl);
		final Pair<List<Expression>, List<Expression>> expressionsA1 = getExpressions(a1, bl);
		
		final Expression disjunctionTerminal0 = genDisjunction(expressionsA0.getFirst(), bl);
		final Expression disjunctionTerminal1 = genDisjunction(expressionsA1.getFirst(), bl);
		final Expression disjunctionNonTerminal0 = genDisjunction(expressionsA0.getSecond(), bl);
		final Expression disjunctionNonTerminal1 = genDisjunction(expressionsA1.getSecond(), bl);
		
		final Expression conjunctionTerminal = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICAND, disjunctionTerminal0, disjunctionTerminal1);
		final Expression conjunctionNonTerminal = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICAND, disjunctionNonTerminal0, disjunctionNonTerminal1);
		
		final Expression disjunction = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICOR, conjunctionTerminal, conjunctionNonTerminal);
		final Expression assertion = ExpressionFactory.constructUnaryExpression(bl, Operator.LOGICNEG, disjunction);
		
		final ReqCheck check = new ReqCheck(Spec.COMPLEMENT);
		final String label = "Complement_" + a0.getName() + "_" + a1.getName();
		return createAssert(assertion, check, label);
	}
	
	private Pair<List<Expression>, List<Expression>>  getExpressions(PhaseEventAutomata pea, BoogieLocation bl) {
		List<Expression>  terminalExpressions = new ArrayList<>();
		List<Expression>  nonTerminalExpressions = new ArrayList<>();
		Pair<List<Expression>, List<Expression>> result = new Pair<List<Expression>, List<Expression>>(terminalExpressions, nonTerminalExpressions);
		Phase[] phases = pea.getPhases();
		for (int i = 0; i < phases.length; i++) {
			Expression expression = genComparePhaseCounter(i, mSymbolTable.getPcName(pea), bl);
			if (phases[i].getTerminal() ) {
				result.getFirst().add(expression);
			} else {
				result.getSecond().add(expression);
			}
		}
		return result;
	}

	@SuppressWarnings("unchecked")
	private List<Statement> genChecksRTInconsistency(final BoogieLocation bl) {
		if (mRtInconcistencyConditionGenerator == null) {
			return Collections.emptyList();
		}

		// get all automata for which conditions should be generated

		final List<Entry<PatternType<?>, PhaseEventAutomata>> consideredAutomata =
				mRtInconcistencyConditionGenerator.getRelevantRequirements(mReqPeas);

		final int count = consideredAutomata.size();

		if (mSeparateInvariantHandling) {
			final long total = mReqPeas.stream().flatMap(a -> a.getCounterTrace2Pea().stream()).count();
			final long invariant = total - count;
			mLogger.info(String.format("%s of %s PEAs are invariant", invariant, total));
		}

		final int actualCombinationNum = mCombinationNum <= count ? mCombinationNum : count;
		if (actualCombinationNum <= 0) {
			mLogger.info("No rt-inconsistencies possible");
			return Collections.emptyList();
		}

		if (mPeaResultUtil.isAlreadyAborted()) {
			throw new ToolchainCanceledException(new RunningTaskInfo(getClass(), "Already encountered errors"));
		}

		final List<Statement> stmtList = new ArrayList<>();
		final List<Entry<PatternType<?>, PhaseEventAutomata>[]> subsets = CrossProducts.subArrays(
				consideredAutomata.toArray(new Entry[count]), actualCombinationNum, new Entry[actualCombinationNum]);
		int subsetsSize = subsets.size();
		if (subsetsSize > 10000) {
			mLogger.warn("Computing rt-inconsistency assertions for " + subsetsSize
					+ " subsets, this might take a while...");
		} else {
			mLogger.info("Computing rt-inconsistency assertions for " + subsetsSize + " subsets");
		}

		long last = System.currentTimeMillis();
		for (final Entry<PatternType<?>, PhaseEventAutomata>[] subset : subsets) {
			if (subsetsSize % 100 == 0 && !mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(),
						"Computing rt-inconsistency assertions, still " + subsetsSize + " left");
			}
			if (subsetsSize % 10 == 0) {
				final long current = System.currentTimeMillis();
				mLogger.info("%s subsets remaining (took %s since last message)", subsetsSize,
						CoreUtil.humanReadableTime(current - last, TimeUnit.MILLISECONDS, 2));
				last = current;
				mRtInconcistencyConditionGenerator.logStats();
			}
			final Statement assertStmt = genAssertRTInconsistency(subset);
			if (assertStmt != null) {
				stmtList.add(assertStmt);
				if (DEBUG_ONLY_FIRST_NON_TRIVIAL_RT_INCONSISTENCY) {
					mLogger.warn(
							"Considering only the first non-trivial rt-inconsistency assertion and skipping all others");
					break;
				}
			}
			subsetsSize--;
		}
		mRtInconcistencyConditionGenerator.logStats();
		return stmtList;
	}

	private Statement genAssertRTInconsistency(final Entry<PatternType<?>, PhaseEventAutomata>[] subset) {
		final Set<PhaseEventAutomata> automataSet = Arrays.stream(subset)
				.map(Entry<PatternType<?>, PhaseEventAutomata>::getValue).collect(Collectors.toSet());
		assert automataSet.size() == subset.length;
		final PhaseEventAutomata[] automata = automataSet.toArray(new PhaseEventAutomata[subset.length]);

		final Expression expr = mRtInconcistencyConditionGenerator.generateNonDeadlockCondition(automata);
		final ReqCheck check = createReqCheck(Spec.RTINCONSISTENT, subset);

		if (expr == null) {
			if (mReportTrivialConsistency) {
				final ILocation loc =
						mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(subset[0].getValue())).getLoc();
				final AssertStatement fakeElem = createAssert(ExpressionFactory.createBooleanLiteral(loc, true), check,
						"RTINCONSISTENT_" + getAssertLabel(subset));
				mPeaResultUtil.intrinsicRtConsistencySuccess(fakeElem);
			}
			return null;
		}

		return createAssert(expr, check, "RTINCONSISTENT_" + getAssertLabel(subset));
	}

	private static String getAssertLabel(final Entry<PatternType<?>, PhaseEventAutomata>[] subset) {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<PatternType<?>, PhaseEventAutomata> entry : subset) {
			sb.append(entry.getValue().getName() + "_");
		}
		return sb.toString();
	}

	private static AssertStatement createAssert(final Expression expr, final ReqCheck check, final String label) {
		final CheckedReqLocation loc = new CheckedReqLocation(check);
		final NamedAttribute[] attr =
				new NamedAttribute[] { new NamedAttribute(loc, "check_" + label, new Expression[] {}) };
		final AssertStatement rtr = new AssertStatement(loc, attr, expr);
		check.annotate(rtr);
		return rtr;
	}

	@Override
	public PeaResultUtil getPeaResultUtil() {
		return mPeaResultUtil;
	}

	private List<Statement> genChecksNonVacuity(final BoogieLocation bl) {
		if (!mCheckVacuity) {
			return Collections.emptyList();
		}

		final List<Statement> stmtList = new ArrayList<>();
		for (final ReqPeas reqpea : mReqPeas) {
			final PatternType<?> pattern = reqpea.getPattern();
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : reqpea.getCounterTrace2Pea()) {
				final Statement assertStmt = genAssertNonVacuous(pattern, pea.getValue(), bl);
				if (assertStmt != null) {
					stmtList.add(assertStmt);
				}
			}
		}
		return stmtList;

	}

	/**
	 * Generate the assertion that is violated if the requirement represented by the given automaton is non-vacuous. The
	 * assertion expresses that the automaton always stays in the early phases and never reaches the last phase. It may
	 * be false if all phases of the automaton are part of the last phase, in which case this function returns null.
	 *
	 * @param req
	 *            The requirement for which vacuity is checked.
	 * @param aut
	 *            The automaton for which vacuity is checked.
	 * @param bl
	 *            A boogie location used for all statements.
	 * @return The assertion for non-vacousness or null if the assertion would be false.
	 */
	private Statement genAssertNonVacuous(final PatternType<?> req, final PhaseEventAutomata aut,
			final BoogieLocation bl) {
		final Phase[] phases = aut.getPhases();

		// compute the maximal phase number occurring in the automaton.
		int maxBits = 0;
		for (final Phase phase : phases) {
			final PhaseBits bits = phase.getPhaseBits();
			// ignore start node when computing max phase
			if (bits != null) {
				final int act = bits.getActive();
				if (act > maxBits) {
					maxBits = act;
				}
			}
		}
		int pnr = 0;
		while (1 << pnr <= maxBits) {
			pnr++;
		}

		// check that one of those phases is eventually reached.
		final List<Expression> checkReached = new ArrayList<>();
		if (pnr > 0) {
			for (int i = 0; i < phases.length; i++) {
				final PhaseBits bits = phases[i].getPhaseBits();
				if (bits == null || (bits.getActive() & (1 << (pnr - 1))) == 0) {
					checkReached.add(genComparePhaseCounter(i, mSymbolTable.getPcName(aut), bl));
				}
			}
		}
		if (checkReached.isEmpty()) {
			return null;
		}
		final Expression disjunction = genDisjunction(checkReached, bl);
		final ReqCheck check = createReqCheck(Spec.VACUOUS, req, aut);
		final String label = "VACUOUS_" + aut.getName();
		return createAssert(disjunction, check, label);
	}

	@SafeVarargs
	private static ReqCheck createReqCheck(final Spec reqSpec,
			final Entry<PatternType<?>, PhaseEventAutomata>... req2pea) {
		if (req2pea == null || req2pea.length == 0) {
			throw new IllegalArgumentException("subset cannot be null or empty");
		}

		final String[] reqIds = new String[req2pea.length];
		final String[] peaNames = new String[req2pea.length];
		for (int i = 0; i < req2pea.length; ++i) {
			reqIds[i] = req2pea[i].getKey().getId();
			peaNames[i] = req2pea[i].getValue().getName();
		}

		return new ReqCheck(reqSpec, reqIds, peaNames);
	}

	private static ReqCheck createReqCheck(final Spec spec, final PatternType<?> req,
			final PhaseEventAutomata aut) {
		return createReqCheck(spec, new Pair<>(req, aut));
	}

	/**
	 * Generate the disjunction of a list of expressions.
	 *
	 * @param exprs
	 *            list of expressions.
	 * @param bl
	 *            Boogie location.
	 * @return the CNF of a list of expressions.
	 */
	private Expression genDisjunction(final List<Expression> exprs, final BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
			return ExpressionFactory.createBooleanLiteral(bl, false);
		}
		Expression cnf = it.next();
		while (it.hasNext()) {
			cnf = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICOR, cnf, it.next());
		}
		return mNormalFormTransformer.toNnf(cnf);
	}

	private Expression genComparePhaseCounter(final int phaseIndex, final String pcName, final BoogieLocation bl) {
		final IdentifierExpression identifier = mSymbolTable.getIdentifierExpression(pcName);
		final IntegerLiteral intLiteral = ExpressionFactory.createIntegerLiteral(bl, Integer.toString(phaseIndex));
		return ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.COMPEQ, identifier, intLiteral);
	}

	@Override
	public List<Statement> getPreChecks() {
		return Collections.emptyList();
	}

	@Override
	public List<Statement> getPostTransitionChecks() {
		return Collections.emptyList();
	}
}
