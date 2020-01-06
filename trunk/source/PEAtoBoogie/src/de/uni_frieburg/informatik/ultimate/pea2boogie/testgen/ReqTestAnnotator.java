package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.util.simplifier.NormalFormTransformer;

public class ReqTestAnnotator implements IReq2PeaAnnotator {
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final PeaResultUtil mPeaResultUtil;
	private final BoogieLocation mLocation;
	private final IReqSymbolTable mSymbolTable;
	private final Map<PatternType, PhaseEventAutomata> mReq2Automata;
	private final Req2CauseTrackingPea mReq2Pea;
	private NormalFormTransformer<Expression> mNormalFormTransformer;
	
	public ReqTestAnnotator(final IUltimateServiceProvider services, final ILogger logger, Req2CauseTrackingPea req2Pea) {
		mLogger = logger;
		mServices = services;	
		mSymbolTable = req2Pea.getSymboltable();
		mReq2Automata = req2Pea.getPattern2Peas();
		mReq2Pea = req2Pea;
		mPeaResultUtil = new PeaResultUtil(mLogger, mServices);
		// TODO: Add locations to pattern type to generate meaningful boogie locations
		mLocation = new BoogieLocation("", -1, -1, -1, -1);
		mNormalFormTransformer = new NormalFormTransformer<>(new BoogieExpressionTransformer());
	}
	
	
	
	@Override
	public List<Statement> getStateChecks() {
		List<Statement> statements = new ArrayList<Statement>();
		Map<PhaseEventAutomata, Integer> pea2EffectPhase = mReq2Pea.getEffectPhase();
		//check that each u_v -> pc_xx == effect(A_r) for every v \in E
		for(String var: mSymbolTable.getStateVars()) {
			if(mSymbolTable.getInputVars().contains(var)) {
				continue;
			}
			if(!mSymbolTable.getStateVars().contains("u_"+var)) {
				//tracking vairable is not used anywhere so do not generate it
				continue;
			}
			for(Map.Entry<PhaseEventAutomata, Set<String>> entry: mReq2Pea.getPea2EffectVars().entrySet()) {
				List<Expression> disjuncts = new ArrayList<>();
				if(entry.getValue().contains(var)) {
					int effectPhase = pea2EffectPhase.get(entry.getKey());
					Expression expr = new BinaryExpression(
							mLocation,
							BinaryExpression.Operator.COMPEQ,
							mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(entry.getKey())),
							new IntegerLiteral(mLocation, Integer.toString(effectPhase)));
					disjuncts.add(expr);
				}
				if(disjuncts.size() > 0) {
					Expression expr = new BinaryExpression(
							mLocation,
							BinaryExpression.Operator.LOGICIMPLIES,
							mSymbolTable.getIdentifierExpression("u_"+var),
							genDisjunction(disjuncts, mLocation));
					statements.add(new AssumeStatement(mLocation, expr));
				}
			}
			
		}	
		//TODO: generate asserts assert(!(pc_xx == i)) for every i \in effect(A_r)
		Map<PhaseEventAutomata, Integer> pea2OutputEffectPhase = mReq2Pea.getOutputEffectPhase();
		for(Map.Entry<PhaseEventAutomata, Integer> entry: pea2OutputEffectPhase.entrySet()) {
			PhaseEventAutomata pea = entry.getKey();
			Expression expr = new BinaryExpression(
					mLocation,
					BinaryExpression.Operator.COMPEQ,
					mSymbolTable.getIdentifierExpression(mSymbolTable.getPcName(pea)),
					new IntegerLiteral(mLocation, entry.getValue().toString()));
			final NamedAttribute[] attr =
					new NamedAttribute[] { new NamedAttribute(mLocation, "TEST_" + pea.getName(), new Expression[] {}) };
			final AssertStatement assrt = 
					new AssertStatement(mLocation, attr, new UnaryExpression(mLocation, Operator.LOGICNEG, expr));
			statements.add(assrt);
		}
		return statements;
	}
	
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

	@Override
	public PeaResultUtil getPeaResultUtil() {
		// TODO Auto-generated method stub
		return null;
	}

}










