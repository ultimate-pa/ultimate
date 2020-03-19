package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieExpressionTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

public class ReqTestAnnotator implements IReq2PeaAnnotator {

	private final ILogger mLogger;
	private final BoogieLocation mLocation;
	private final IReqSymbolTable mSymbolTable;
	private final Req2CauseTrackingPea mReq2Pea;
	private final NormalFormTransformer<Expression> mNormalFormTransformer;
	private final Map<PhaseEventAutomata, ReqEffectStore> mPea2EffectStore;

	public static final String TEST_ASSERTION_PREFIX = "testgen_";
	public static final String INITIAL_STEP_FLAG = "testgen_initial_step_flag";
	public static final String TRACKING_VAR_PREFIX = "u_";

	public ReqTestAnnotator(final IUltimateServiceProvider services, final ILogger logger,
			final Req2CauseTrackingPea req2Pea) {
		mLogger = logger;
		mSymbolTable = req2Pea.getSymboltable();
		mReq2Pea = req2Pea;
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		mLocation = new BoogieLocation("", -1, -1, -1, -1);
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		mPea2EffectStore = mReq2Pea.getReqEffectStore();
	}

	@Override
	public List<Statement> getStateChecks() {
		final List<Statement> statements = new ArrayList<>();
		// check that each u_v -> pc_xx == effect(A_r) for every v \in E
		statements.addAll(genTrackingAssumptions());
		return statements;
	}

	@Override
	public List<Statement> getPostTransitionChecks() {
		final List<Statement> statements = new ArrayList<>();
		// generate asserts assert(!(pc_xx == i)) for every i \in effect(A_r)
		statements.addAll(genTestAssertions());
		statements.add(new AssignmentStatement(mLocation,
				new LeftHandSide[] {mSymbolTable.getVariableLhs(mSymbolTable.getPrimedVarId(INITIAL_STEP_FLAG))},
				new Expression[] {new BooleanLiteral(mLocation, false)}
				));
		return statements;
	}

	@Override
	public List<Statement> getPreChecks() {
		final List<Statement> statements = new ArrayList<>();
		// check that each u_v -> pc_xx == effect(A_r) for every v \in E
		//statements.addAll(genTrackingAssumptions());
		return statements;
	}

	public static String getTrackingVar(String ident) {
		return TRACKING_VAR_PREFIX + ident;
	}

	/*
	 * Generates an assumption that implies that if the aux var u_v (prefix "u_", for each v in statevars)
	 * then at least one PEA is in an effect phase or on an edge that (whose guard/invariant) determines the value
	 * of v.
	 */
	private List<Statement> genTrackingAssumptions() {
		final List<Statement> statements = new ArrayList<>();
		for (final String trackedVar : mSymbolTable.getStateVars()) {
			final List<Expression> disjuncts = new ArrayList<>();
			final List<Expression> primedDisjuncts = new ArrayList<>();
			final String trackingVar = getTrackingVar(trackedVar);
			if (mSymbolTable.getInputVars().contains(trackedVar)) {
				continue;
			}
			if (!mSymbolTable.getStateVars().contains(trackingVar) && !mSymbolTable.getOutputVars().contains(trackedVar)) {
				// the tracking variable was never used and is no output where tracking
				//is relevant for test formatting thus there is no need generating the invariant
				continue;
			}
			for (final Map.Entry<PhaseEventAutomata, ReqEffectStore> entry : mPea2EffectStore.entrySet()) {
				if (entry.getValue().getEffectVars().contains(trackedVar)) {
					disjuncts.addAll(genPhaseTrackingDisjuncts(entry.getKey(), trackedVar));
					primedDisjuncts.addAll(genTransitionTrackingDisjuncts(entry.getKey(), trackedVar));
				}
			}
			if (disjuncts.size() > 0) {
				final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICIFF,
						mSymbolTable.getIdentifierExpression(trackingVar), genDisjunction(disjuncts, mLocation));
				statements.add(new AssumeStatement(mLocation, expr));
			}
			if (primedDisjuncts.size() > 0) {
				final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICIFF,
						mSymbolTable.getIdentifierExpression(mSymbolTable.getPrimedVarId(trackingVar)),
						genDisjunction(primedDisjuncts, mLocation));
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
		//disjuncts.add(mSymbolTable.getIdentifierExpression(mSymbolTable.getPrimedVarId(INITIAL_STEP_FALG)));
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
		if (mPea2EffectStore.get(pea).isEffectPhaseIndex(phaseNum)) {
			final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, phaseNum.toString()));
			disjuncts.add(expr);
		}
		return disjuncts;
	}

	private List<Expression> genTransitionEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer sourceIndex) {
		final List<Expression> disjuncts = new ArrayList<>();
		final List<Phase> phaseList = Arrays.asList(pea.getPhases());
		for (final Transition transition : phaseList.get(sourceIndex).getTransitions()) {
			final Integer destIndex = phaseList.indexOf(transition.getDest());
			if (mPea2EffectStore.get(pea).isEffectEdge(sourceIndex, destIndex)) {
				disjuncts.add(genTransitionSucceedingTracking(pea, sourceIndex, destIndex));
			}
		}
		return disjuncts;
	}

	private Expression genTransitionSucceedingTracking(final PhaseEventAutomata pea, final Integer sourceIndex,
			final Integer destIndex) {
		final Expression thisExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
				new IntegerLiteral(mLocation, sourceIndex.toString()));
		final Expression nextExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getPrimedVarId(mSymbolTable.getPcName(pea))),
				new IntegerLiteral(mLocation, Integer.toString(destIndex)));
		final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, thisExpr, nextExpr);
		return expr;
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
			statements.addAll(genTestPhaseEffectAssertion(entry.getKey(), entry.getValue().getOutputEffectPhaseIndex()));
			//statements.addAll(genTestEdgeEffectAssertion(entry.getKey(), entry.getValue().getEffectEdges()));
		}
		return statements;
	}

	/*
	 * returns assertions that are fulfilled if the effect phase of the tracking automaton is left (and does not enter
	 * another phase being an effect phase).
	 */
	private List<Statement> genTestPhaseEffectAssertion(final PhaseEventAutomata pea, final Set<Integer> effectPhases) {
		final List<Statement> statements = new ArrayList<>();
		for(final int effectPhaseIndex: effectPhases) {
			final Expression thisExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, Integer.toString(effectPhaseIndex)));
			final Expression nextExpr = genIdentNotInSet(
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPrimedVarId(mSymbolTable.getPcName(pea))), effectPhases);
			final Expression leavingPhaseAssertion =
					new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, thisExpr, nextExpr);
			final NamedAttribute[] attr = new NamedAttribute[] {
					new NamedAttribute(mLocation, TEST_ASSERTION_PREFIX + pea.getName() + Integer.toString(effectPhaseIndex), new Expression[] {}) };
			final Statement assrt = new AssertStatement(mLocation, attr,
					new UnaryExpression(mLocation, UnaryExpression.Operator.LOGICNEG, leavingPhaseAssertion));
			statements.add(assrt);
		}
		return statements;
	}

	private Expression genIdentNotInSet(final IdentifierExpression ident, final Set<Integer> notInSet) {
		Expression ret = new BooleanLiteral(mLocation, true);
		for(final int notEqInt: notInSet) {
			final Expression comparison = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPNEQ, ident,
					new IntegerLiteral(mLocation, Integer.toString(notEqInt)));
			ret = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, ret, comparison);
		}
		return ret;
	}

	private List<Statement> genTestEdgeEffectAssertion(final PhaseEventAutomata pea,
			final Map<Integer, Integer> effectEdges) {
		// for effects on edges use pc== /\ u_v so we know we walked over the edge and are in the state the effect
		// maifests in
		final List<Statement> statements = new ArrayList<>();
		for (final Map.Entry<Integer, Integer> edgeIndexes : effectEdges.entrySet()) {
			final String testName = "prefail_" + pea.getName() + Integer.toString(edgeIndexes.getValue()) + "_"
					+ Integer.toString(edgeIndexes.getKey()) + "'";
			final Expression thisExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, Integer.toString(edgeIndexes.getKey())));
			final Expression nextExpr = new BinaryExpression(mLocation, BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea) + "'"),
					new IntegerLiteral(mLocation, Integer.toString(edgeIndexes.getValue())));
			final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICIMPLIES,
					mSymbolTable.getIdentifierExpression(testName),
					new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, thisExpr, nextExpr));
			statements.add(new AssumeStatement(mLocation, expr));
			final NamedAttribute[] attr = new NamedAttribute[] {
					new NamedAttribute(mLocation, TEST_ASSERTION_PREFIX + pea.getName(), new Expression[] {}) };
			final Statement assrt = new AssertStatement(mLocation, attr,
					new UnaryExpression(mLocation, Operator.LOGICNEG, mSymbolTable.getIdentifierExpression(testName)));
			statements.add(assrt);
		}

		return statements;
	}

	@Override
	public PeaResultUtil getPeaResultUtil() {
		// TODO Auto-generated method stub
		return null;
	}

}
