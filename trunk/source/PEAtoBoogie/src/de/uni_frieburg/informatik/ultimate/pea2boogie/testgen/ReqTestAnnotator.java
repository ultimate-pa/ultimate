package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

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
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
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

	public static final String TEST_ASSERTION_PREFIX = "TEST_";

	public ReqTestAnnotator(final IUltimateServiceProvider services, final ILogger logger, final Req2CauseTrackingPea req2Pea) {
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
		final List<Statement> statements = new ArrayList<Statement>();
		//check that each u_v -> pc_xx == effect(A_r) for every v \in E
		statements.addAll(genTrackingAssumptions());
		//generate asserts assert(!(pc_xx == i)) for every i \in effect(A_r)
		statements.addAll(genTestAssertions());
		return statements;
	}

	@Override
	public List<Statement> getPreChecks(){
		final List<Statement> statements = new ArrayList<Statement>();
		//check that each u_v -> pc_xx == effect(A_r) for every v \in E
		statements.addAll(genTrackingAssumptions());
		return statements;
	}

	private List<Statement> genTrackingAssumptions(){
		final List<Statement> statements = new ArrayList<Statement>();
		for(final String trackedVar: mSymbolTable.getStateVars()) {
			final List<Expression> disjuncts = new ArrayList<>();
			final List<Expression> primedDisjuncts = new ArrayList<>();
			if(mSymbolTable.getInputVars().contains(trackedVar)) {
				continue;
			}
			if(!mSymbolTable.getStateVars().contains("u_"+trackedVar)) {
				//the tracking variable was never used and thus there is no need generating the invariant
				continue;
			}
			for(final Map.Entry<PhaseEventAutomata, ReqEffectStore> entry: mPea2EffectStore.entrySet()) {
				if (entry.getValue().getEffectVars().contains(trackedVar)) {
					disjuncts.addAll(genTrackingDisjuncts(entry.getKey(), trackedVar));
					primedDisjuncts.addAll(genTransitionTrackingDisjuncts(entry.getKey(), trackedVar));
				}
			}
			if(disjuncts.size() > 0) {
				final Expression expr = new BinaryExpression(
						mLocation,
						BinaryExpression.Operator.LOGICIMPLIES,
						mSymbolTable.getIdentifierExpression("u_"+trackedVar),
						genDisjunction(disjuncts, mLocation));
				statements.add(new AssumeStatement(mLocation, expr));
			}
			if(primedDisjuncts.size() > 0) {
				final Expression expr = new BinaryExpression(
						mLocation,
						BinaryExpression.Operator.LOGICIMPLIES,
						mSymbolTable.getIdentifierExpression("u_"+trackedVar+"'"),
						genDisjunction(primedDisjuncts, mLocation));
				statements.add(new AssumeStatement(mLocation, expr));
			}
		}
		return statements;
	}

	private List<Expression> genTrackingDisjuncts(final PhaseEventAutomata pea, final String currentVar) {
		final List<Expression> disjuncts = new ArrayList<>();
		for(final Integer phaseNum: mPea2EffectStore.get(pea).getEffectPhaseIndexes()) {
			disjuncts.addAll(genPhaseEffectTracking(pea, currentVar, phaseNum));

		}
		return disjuncts;
	}

	private List<Expression> genTransitionTrackingDisjuncts(final PhaseEventAutomata pea, final String currentVar) {
		final List<Expression> disjuncts = new ArrayList<>();
		for(final Integer phaseNum: mPea2EffectStore.get(pea).getEffectEdgeSourceIndexes()) {
			disjuncts.addAll(genTransitionEffectTracking(pea, currentVar, phaseNum));
		}
		return disjuncts;
	}

	private List<Expression> genPhaseEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer phaseNum){
		final List<Expression> disjuncts = new ArrayList<>();
		if(mPea2EffectStore.get(pea).isEffectPhaseIndex(phaseNum)) {
			final Expression expr = new BinaryExpression(
					mLocation,
					BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, phaseNum.toString()));
			disjuncts.add(expr);
		}
		return disjuncts;
	}

	private List<Expression> genTransitionEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer sourceIndex){
		final List<Expression> disjuncts = new ArrayList<>();
		final List<Phase> phaseList =  Arrays.asList(pea.getPhases());
		for(final Transition transition: phaseList.get(sourceIndex).getTransitions()) {
			final Integer destIndex = phaseList.indexOf(transition.getDest());
			if(mPea2EffectStore.get(pea).isEffectEdge(sourceIndex, destIndex)) {
				disjuncts.add(genTransitionSucceedingTracking(pea, sourceIndex, destIndex, phaseList));
			}
		}
		return disjuncts;
	}

	private Expression genTransitionSucceedingTracking(final PhaseEventAutomata pea, final Integer sourceIndex,
			final Integer destIndex, final List<Phase> phaseList) {
		final Expression thisExpr = new BinaryExpression(
				mLocation,
				BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
				new IntegerLiteral(mLocation, sourceIndex.toString()));
		final Expression nextExpr = new BinaryExpression(
				mLocation,
				BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea) + "'"),
				new IntegerLiteral(mLocation, Integer.toString(destIndex)));
		final Expression expr = new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, thisExpr, nextExpr);
		mLogger.error(expr.toString());
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
			//cnf = ExpressionFactory.newBinaryExpression(bl, BinaryExpression.Operator.LOGICOR, cnf, it.next());
		}
		return mNormalFormTransformer.toNnf(cnf);
	}

	private  List<Statement> genTestAssertions(){
		final List<Statement> statements = new ArrayList<Statement>();

		//for(final Map.Entry<PhaseEventAutomata, Set<Integer>> entry: pea2OutputEffectPhase.entrySet()) {
		for(final Map.Entry<PhaseEventAutomata, ReqEffectStore> entry: mPea2EffectStore.entrySet()) {
			statements.addAll(genTestAssertion(entry.getKey(), entry.getValue().getOutputEffectPhaseIndex()));
		}
		return statements;
	}

	private List<Statement> genTestAssertion(final PhaseEventAutomata pea, final Set<Integer> effectPhases){
		//TODO see trackingFlags on edges, same here for the regarding automta
		// for effects on edges use pc== /\ u_v so we know we walked over the edge and are in the state the effect maifests in
		final List<Statement> statements = new ArrayList<Statement>();
		for (final Integer phaseNr: effectPhases) {
			final Expression expr = new BinaryExpression(
					mLocation,
					BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, phaseNr.toString()));
			final NamedAttribute[] attr =
					new NamedAttribute[] { new NamedAttribute(mLocation, TEST_ASSERTION_PREFIX + pea.getName(), new Expression[] {}) };
			final AssertStatement assrt =
					new AssertStatement(mLocation, attr, new UnaryExpression(mLocation, Operator.LOGICNEG, expr));
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










