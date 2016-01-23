package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class OctPostOperator implements IAbstractPostOperator<OctagonDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;
	private final RcfgStatementExtractor mStatementExtractor;
	private final OctStatementProcessor mStatementProcessor;
	private final BoogieSymbolTable mSymbolTable;

	public OctPostOperator(Logger logger, BoogieSymbolTable symbolTable) {
		mLogger = logger;
		mStatementExtractor = new RcfgStatementExtractor();
		mStatementProcessor = new OctStatementProcessor(mLogger, symbolTable);
		mSymbolTable = symbolTable;
	}

	@Override
	public List<OctagonDomainState> apply(OctagonDomainState oldState, CodeBlock codeBlock) {
		List<OctagonDomainState> currentState = Collections.singletonList(oldState.deepCopy());
//		List<OctagonDomainState> currentState = new ArrayList<>();
//		currentState.add(oldState);
		for (Statement statement : mStatementExtractor.process(codeBlock)) {
			currentState = mStatementProcessor.process(currentState, statement);
		}
		return currentState;
	}
	
	private OctagonDomainState join(List<OctagonDomainState> states) {
		assert states.size() > 0 : "nothing to join";
		OctagonDomainState joinedState = null;
		for (OctagonDomainState result : states) {
			if (joinedState == null) {
				joinedState = result;
			} else {
				joinedState = joinedState.join(result);
			}
		}
		return joinedState;
	}

	@Override
	public List<OctagonDomainState> apply(OctagonDomainState stateBeforeLeaving, OctagonDomainState stateAfterLeaving,
			CodeBlock transition) {
		OctagonDomainState result;
		if (transition instanceof Call) {
			result = applyCall(stateBeforeLeaving, stateAfterLeaving, (Call) transition);
		} else if (transition instanceof Return) {
			result = applyReturn(stateBeforeLeaving, stateAfterLeaving, (Return) transition);
		} else {
			throw new UnsupportedOperationException("Unsupported transition: " + transition);
		}
		return Collections.singletonList(result);
	}

	private OctagonDomainState applyCall(OctagonDomainState stateBeforeLeaving, OctagonDomainState stateAfterLeaving,
			Call callTransition) {
		CallStatement call = callTransition.getCallStatement();
		Procedure procedure = calledProcedure(call);

		Map<String, String> mapArgToInParam = new HashMap<>();

		// TODO evaluate expressions
//		for (Expression expr : call.getArguments()) {
//			
//		}
		// TODO assign evaluated expressions to <insert state here>.
		// probably best to project and assign separately
		
//		return stateAfterLeaving.copyValuesOnScopeChange(stateBeforeLeaving, mapArgToInParam);

		// HACK -- assume \top for all in-params (valid but poor over-approximation)
		OctagonDomainState newState = stateAfterLeaving.deepCopy();
		for (VarList inParamList : procedure.getInParams()) {
			for (String inParam : inParamList.getIdentifiers()) {
				newState.havocVar(inParam);
			}
		}
		return newState;
	}
	
	private OctagonDomainState applyReturn(OctagonDomainState stateBeforeLeaving, OctagonDomainState stateAfterLeaving,
			Return returnTransition) {
		CallStatement call = returnTransition.getCallStatement();
		Procedure procedure = calledProcedure(call);
		Map<String, String> mapOutToLhs = generateMapOutToLhs(call.getLhs(), procedure);
		return stateAfterLeaving.copyValuesOnScopeChange(stateBeforeLeaving, mapOutToLhs);
	}
	
	private Procedure calledProcedure(CallStatement call) {
		List<Declaration> procedureDeclarations = mSymbolTable.getFunctionOrProcedureDeclaration(call.getMethodName());
		Procedure implementation = null;
		for (Declaration d : procedureDeclarations) {
			assert d instanceof Procedure : "call/return of non-procedure " + call.getMethodName() + ": " + d;
			Procedure p = (Procedure) d;
			if (p.getBody() != null) {
				if (implementation != null) {
					throw new UnsupportedOperationException("Multiple implementations of " + call.getMethodName());
				}
				implementation = p;
			}
		}
		if (implementation == null) {
			throw new UnsupportedOperationException("Missing implementation of " + call.getMethodName());
		}
		return implementation;
	}
	
	private Map<String, String> generateMapOutToLhs(VariableLHS[] lhs, Procedure calledProcedure) {
			Map<String, String> mapOutToLhs = new HashMap<>();
		// out-parameters to lhs of call assignment
		int i = 0;
		for (VarList outParamList : calledProcedure.getOutParams()) {
			for (String oudParam : outParamList.getIdentifiers()) {
				assert i < lhs.length : "missing left hand side for out-parameter";
				mapOutToLhs.put(oudParam, lhs[i].getIdentifier());
				++i;
			}
		}
		assert i == lhs.length : "missing out-parameter for left hand side";
		return mapOutToLhs;
	}
	
}
