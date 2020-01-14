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
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

public class ReqTestAnnotator implements IReq2PeaAnnotator {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final BoogieLocation mLocation;
	private final IReqSymbolTable mSymbolTable;
	private final Map<PatternType, PhaseEventAutomata> mReq2Automata;
	private final Req2CauseTrackingPea mReq2Pea;
	private final NormalFormTransformer<Expression> mNormalFormTransformer;
	final Req2CauseTrackingCDD mCddTransformer;

	public static final String TEST_ASSERTION_PREFIX = "TEST_";

	public ReqTestAnnotator(final IUltimateServiceProvider services, final ILogger logger, final Req2CauseTrackingPea req2Pea) {
		mLogger = logger;
		mServices = services;
		mSymbolTable = req2Pea.getSymboltable();
		mReq2Automata = req2Pea.getPattern2Peas();
		mReq2Pea = req2Pea;
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		mLocation = new BoogieLocation("", -1, -1, -1, -1);
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());
		mCddTransformer = new Req2CauseTrackingCDD(mLogger);
	}

	@Override
	public List<Statement> getStateChecks() {
		final List<Statement> statements = new ArrayList<Statement>();
		//generate asserts assert(!(pc_xx == i)) for every i \in effect(A_r)
		statements.addAll(genTestAssertions());
		//check that each u_v' -> pc_xx == effect(A_r) for every v' \in E'
		statements.addAll(genTrackingAssumptions(""));
		return statements;
	}

	@Override
	public List<Statement> getPreChecks(){
		final List<Statement> statements = new ArrayList<Statement>();
		//check that each u_v -> pc_xx == effect(A_r) for every v \in E
		statements.addAll(genTrackingAssumptions(""));
		return statements;
	}

	private List<Statement> genTrackingAssumptions(String primed){
		final List<Statement> statements = new ArrayList<Statement>();
		for(final String trackedVar: mSymbolTable.getStateVars()) {
			final List<Expression> disjuncts = new ArrayList<>();
			if(mSymbolTable.getInputVars().contains(trackedVar)) {
				continue;
			}
			if(!mSymbolTable.getStateVars().contains("u_"+trackedVar)) {
				//the tracking variable was never used and thus there is no need generating the invariant
				continue;
			}
			for(final Map.Entry<PhaseEventAutomata, Set<String>> entry: mReq2Pea.getPea2EffectVars().entrySet()) {
				if (entry.getValue().contains(trackedVar)) {
					disjuncts.addAll(genTrackingDisjuncts(entry.getKey(), trackedVar, primed));
				}
			}
			if(disjuncts.size() > 0) {
				final Expression expr = new BinaryExpression(
						mLocation,
						BinaryExpression.Operator.LOGICIMPLIES,
						mSymbolTable.getIdentifierExpression("u_"+trackedVar+primed),
						genDisjunction(disjuncts, mLocation));
				statements.add(new AssumeStatement(mLocation, expr));
			}
		}
		return statements;
	}

	private List<Expression> genTrackingDisjuncts(final PhaseEventAutomata pea, final String currentVar, String primed) {
		final List<Expression> disjuncts = new ArrayList<>();
		final Map<PhaseEventAutomata, Set<Integer>> pea2EffectPhase = mReq2Pea.getEffectPhase();
		for(final Integer phaseNum: pea2EffectPhase.get(pea)) {
			//determine if the effect is part of the phase, or if the effect is on each outgoing edge
			// then either generate the following OR generate a u_v' -> (pc == n && pc' == NONEFFSTATE) || ...
			// i.e. we were in the effect state waiting to leave, and now we have left over an edge that has an effect
			//disjuncts.addAll(genEdgeEffectTracking(pea, currentVar, phaseNum, primed));
			disjuncts.addAll(genPhaseEffectTracking(pea, currentVar, phaseNum, primed));
		}
		return disjuncts;
	}

	private List<Expression> genPhaseEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer phaseNum, final String primed){
		final List<Expression> disjuncts = new ArrayList<>();
		if(isEffectPhase(pea, phaseNum)) {
			final Expression expr = new BinaryExpression(
					mLocation,
					BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)+primed),
					new IntegerLiteral(mLocation, phaseNum.toString()));
			disjuncts.add(expr);
		}
		return disjuncts;
	}

	private List<Expression> genEdgeEffectTracking(final PhaseEventAutomata pea, final String currentVar,
			final Integer phaseNum, final String primed){
		final List<Expression> disjuncts = new ArrayList<>();
		final List<Phase> phaseList =  Arrays.asList(pea.getPhases());
		for(final Transition transition: phaseList.get(phaseNum).getTransitions()) {
			if(isEffectTransition(transition, currentVar)) {
				disjuncts.add(genTransitionSucceedingTracking(pea, transition, phaseNum, phaseList, primed));
			}
		}
		return disjuncts;
	}

	private Expression genTransitionSucceedingTracking(final PhaseEventAutomata pea, final Transition transition,
			final Integer phaseNum, final List<Phase> phaseList, final String primed) {
		final Expression thisExpr = new BinaryExpression(
				mLocation,
				BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
				new IntegerLiteral(mLocation, phaseNum.toString()));
		final Expression nextExpr = new BinaryExpression(
				mLocation,
				BinaryExpression.Operator.COMPEQ,
				mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)+primed),
				new IntegerLiteral(mLocation, Integer.toString(phaseList.indexOf(transition.getDest())) ));
		return new BinaryExpression(mLocation, BinaryExpression.Operator.LOGICAND, thisExpr, nextExpr);
	}


	private boolean isEffectTransition(Transition transition, String currentVar){
		return mCddTransformer.getCddVariables(transition.getGuard()).contains(currentVar);

	}

	private boolean isEffectPhase(final PhaseEventAutomata pea, final Integer phaseNum){
		return true;
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
		final Map<PhaseEventAutomata, Set<Integer>> pea2OutputEffectPhase = mReq2Pea.getOutputEffectPhase();
		for(final Map.Entry<PhaseEventAutomata, Set<Integer>> entry: pea2OutputEffectPhase.entrySet()) {
			statements.addAll(genTestAssertion(entry.getKey(), entry.getValue()));
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










