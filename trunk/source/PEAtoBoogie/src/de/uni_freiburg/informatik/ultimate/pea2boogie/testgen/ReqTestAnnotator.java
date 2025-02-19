package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.StrictInvariant;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.CDDTranslator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

public class ReqTestAnnotator implements IReq2PeaAnnotator {

	private final BoogieLocation mLocation;
	private final IReqSymbolTable mSymbolTable;
	private final Req2CauseTrackingPea mReq2Pea;
	private final NormalFormTransformer<Expression> mNormalFormTransformer;
	private final Map<PhaseEventAutomata, ReqEffectStore> mPea2EffectStore;

	public static final String TEST_ASSERTION_PREFIX = "testgen_";
	public static final String TRACKING_VAR_PREFIX = "u_";

	public ReqTestAnnotator(final IUltimateServiceProvider services, final ILogger logger,
			final Req2CauseTrackingPea req2Pea) {
		mSymbolTable = req2Pea.getSymboltable();
		mReq2Pea = req2Pea;
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		mLocation = new BoogieLocation("", -1, -1, -1, -1);
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		mPea2EffectStore = mReq2Pea.getReqEffectStore();
	}

	@Override
	public List<Statement> getStateChecks() {
		final List<Statement> statements = new ArrayList<>(genTrackingAssumptions());
		statements.addAll(genTestAssertions());
		return statements;
	}

	@Override
	public List<Statement> getPostTransitionChecks() {
		return Collections.emptyList();
	}

	@Override
	public List<Statement> getPreChecks() {
		return new ArrayList<>();
	}

	public static String getTrackingVar(final String ident) {
		return TRACKING_VAR_PREFIX + ident;
	}

	/*
	 * Generates an assumption that implies that if the aux var u_v (prefix "u_", for each v in statevars) then at least
	 * one PEA is in an effect phase or on an edge that (whose guard/invariant) determines the value of v.
	 */
	private List<Statement> genTrackingAssumptions() {
		final List<Statement> statements = new ArrayList<>();
		for (final String trackedVar : mSymbolTable.getStateVars()) {
			final List<Expression> disjuncts = new ArrayList<>();
			final String trackingVar = getTrackingVar(trackedVar);
			if (mSymbolTable.getInputVars().contains(trackedVar) || !mSymbolTable.getStateVars().contains(trackingVar)
					&& !mSymbolTable.getOutputVars().contains(trackedVar)) {
				// the tracking variable was never used and is no output where tracking
				// is relevant for test formatting thus there is no need generating the invariant
				continue;
			}
			for (final Map.Entry<PhaseEventAutomata, ReqEffectStore> entry : mPea2EffectStore.entrySet()) {
				if (entry.getValue().getEffectVars().contains(trackedVar)) {
					disjuncts.addAll(genPhaseTrackingDisjuncts(entry.getKey(), trackedVar));
					disjuncts.addAll(genTransitionTrackingDisjuncts(entry.getKey(), trackedVar));
				}
			}
			if (disjuncts.size() > 0) {
				final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICIMPLIES,
						mSymbolTable.getIdentifierExpression(trackingVar), genDisjunction(disjuncts, mLocation));
				statements.add(new AssumeStatement(mLocation, expr));
			}
		}
		return statements;
	}

	private List<Expression> genPhaseTrackingDisjuncts(final PhaseEventAutomata pea, final String currentVar) {
		final List<Expression> disjuncts = new ArrayList<>();
		for (final Integer phaseNum : mPea2EffectStore.get(pea).getEffectPhaseIndexes()) {
			disjuncts.addAll(genPhaseEffectTracking(pea, currentVar, phaseNum));
		}
		return disjuncts;
	}

	private List<Expression> genTransitionTrackingDisjuncts(final PhaseEventAutomata pea, final String currentVar) {
		final List<Expression> disjuncts = new ArrayList<>();
		for (final Integer phaseNum : mPea2EffectStore.get(pea).getEffectEdgeSourceIndexes()) {
			disjuncts.addAll(genTransitionEffectTracking(pea, currentVar, phaseNum));
		}
		return disjuncts;
	}

	private List<Expression> genPhaseEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer phaseNum) {
		final List<Expression> disjuncts = new ArrayList<>();
		final String pc = mSymbolTable.getPcName(pea);
		if (mPea2EffectStore.get(pea).isEffectPhaseIndex(phaseNum)) {
			final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(pc), new IntegerLiteral(mLocation, phaseNum.toString()));
			disjuncts.add(expr);
		}
		return disjuncts;
	}

	/*
	 * 'pc = source /\ pc = target for each edge with an E' (effect) guard
	 */
	private List<Expression> genTransitionEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer sourceIndex) {
		final List<Expression> disjuncts = new ArrayList<>();
		final List<Phase> phaseList = pea.getPhases();
		for (final Transition transition : phaseList.get(sourceIndex).getTransitions()) {
			final Integer destIndex = phaseList.indexOf(transition.getDest());
			if (mPea2EffectStore.get(pea).isEffectEdge(sourceIndex, destIndex)) {
				disjuncts.add(genTransitionSucceedingTracking(pea, sourceIndex, destIndex));
			}
		}
		return disjuncts;
	}

	/*
	 * 'pc = source /\ pc = target
	 */
	private Expression genTransitionSucceedingTracking(final PhaseEventAutomata pea, final Integer sourceIndex,
			final Integer destIndex) {
		final String peaName = mSymbolTable.getPcName(pea);
		final Expression lastExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getHistoryVarId(peaName)),
				new IntegerLiteral(mLocation, sourceIndex.toString()));
		final Expression thisExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(peaName),
				new IntegerLiteral(mLocation, Integer.toString(destIndex)));
		return new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, lastExpr, thisExpr);
	}

	private Expression genDisjunction(final List<Expression> exprs, final BoogieLocation bl) {
		final Iterator<Expression> it = exprs.iterator();
		if (!it.hasNext()) {
			return ExpressionFactory.createBooleanLiteral(bl, false);
		}
		Expression cnf = it.next();
		while (it.hasNext()) {
			cnf = new BinaryExpression(bl, BinaryExpression.Operator.LOGICOR, cnf, it.next());
			// cnf = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICOR, cnf, it.next());
		}
		return mNormalFormTransformer.toNnf(cnf);
	}

	private List<Statement> genTestAssertions() {
		final List<Statement> statements = new ArrayList<>();
		for (final Map.Entry<PhaseEventAutomata, ReqEffectStore> entry : mPea2EffectStore.entrySet()) {
			statements
					.addAll(genTestPhaseEffectAssertion(entry.getKey(), entry.getValue().getOutputEffectPhaseIndex()));
			statements.addAll(genTestEdgeEffectAssertion(entry.getKey(), entry.getValue().getOutputEffectEdges()));
		}
		return statements;
	}

	/*
	 * returns assertions that are fulfilled if the effect phase of the tracking automaton is left (and does not enter
	 * another phase being an effect phase).
	 */
	private List<Statement> genTestPhaseEffectAssertion(final PhaseEventAutomata pea, final Set<Integer> effectPhases) {
		final List<Statement> statements = new ArrayList<>();
		for (final int effectPhaseIndex : effectPhases) {
			final String pcName = mSymbolTable.getPcName(pea);
			final Expression inLocationExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getHistoryVarId(pcName)),
					new IntegerLiteral(mLocation, Integer.toString(effectPhaseIndex)));
			final CDD clockInvar = pea.getLocation(effectPhaseIndex).getClockInvariant();
			Expression timeToLeave = new BooleanLiteral(mLocation, true);
			if (clockInvar != CDD.TRUE) {
				final CDD strictInvar = new StrictInvariant().genStrictInv(clockInvar, Collections.emptySet());
				timeToLeave = new CDDTranslator().toBoogie(strictInvar.negate(), mLocation);
			}
			final Expression leavingPhaseAssertion =
					new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, timeToLeave, inLocationExpr);
			final NamedAttribute[] attr = { new NamedAttribute(mLocation,
					TEST_ASSERTION_PREFIX + pea.getName() + Integer.toString(effectPhaseIndex), new Expression[] {}) };
			final Statement assrt = new AssertStatement(mLocation, attr,
					new UnaryExpression(mLocation, UnaryExpression.Operator.LOGICNEG, leavingPhaseAssertion));
			statements.add(assrt);
		}
		return statements;
	}

	/**
	 * Test Generator assertion for edges with effects: check if an effect edge has been used in the last configuration
	 * i.e. now there is an effect determining the variable
	 */
	private List<Statement> genTestEdgeEffectAssertion(final PhaseEventAutomata pea,
			final Set<Pair<Integer, Integer>> effectEdges) {
		final List<Statement> statements = new ArrayList<>();
		for (final Pair<Integer, Integer> edgeIndexes : effectEdges) {
			final Expression lastExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getHistoryVarId(mSymbolTable.getPcName(pea))),
					new IntegerLiteral(mLocation, Integer.toString(edgeIndexes.getKey())));
			final Expression thisExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, Integer.toString(edgeIndexes.getValue())));
			final Expression overEdgeIndexes =
					new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, thisExpr, lastExpr);
			final NamedAttribute[] attr =
					{ new NamedAttribute(mLocation, TEST_ASSERTION_PREFIX + pea.getName(), new Expression[] {}) };
			final Statement assume = new AssertStatement(mLocation, attr,
					new UnaryExpression(mLocation, Operator.LOGICNEG, overEdgeIndexes));
			statements.add(assume);
		}

		return statements;
	}

	@Override
	public PeaResultUtil getPeaResultUtil() {
		return null;
	}

}
