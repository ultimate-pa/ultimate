package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
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
	public OctagonDomainState apply(OctagonDomainState oldState, CodeBlock codeBlock) {
		OctagonDomainState currentState = oldState;
		for (Statement statement : mStatementExtractor.process(codeBlock)) {
			currentState = join(mStatementProcessor.process(currentState, statement));
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
	public OctagonDomainState apply(OctagonDomainState stateBeforeLeaving, OctagonDomainState stateAfterLeaving,
			CodeBlock transition) {
		if (transition instanceof Call) {
			return stateAfterLeaving;
		} else if (transition instanceof Return) {
			return applyReturn(stateBeforeLeaving, stateAfterLeaving, (Return) transition);
		} else {
			throw new UnsupportedOperationException("Unsupported transition: " + transition);
		}
//		throw new UnsupportedOperationException("Not yet implemented");
	}
	
	private OctagonDomainState applyReturn(OctagonDomainState stateBeforeLeaving, OctagonDomainState stateAfterLeaving,
			Return ret) {
		CallStatement call = ret.getCallStatement();
		List<Declaration> procedureDeclarations = mSymbolTable.getFunctionOrProcedureDeclaration(call.getMethodName());
		assert procedureDeclarations.size() > 0 : "return from undefined method";
		if (procedureDeclarations.size() > 1) {
			throw new UnsupportedOperationException("Separated implementations are unsupported.");
		}
		assert procedureDeclarations.get(0) instanceof Procedure : "return from non-procedure";
		Procedure procedure = (Procedure) procedureDeclarations.get(0);

		Map<String, String> mapOutToLhs = generateMapOutToLhs(call.getLhs(), procedure);

		// TODO copy output vars to lhs
		
//		return null;
		throw new UnsupportedOperationException("work in progress");
	}
	
	private Map<String, String> generateMapOutToLhs(VariableLHS[] lhs, Procedure calledProcedure) {
		Map<String, String> mapOutToLhs = new HashMap<>();
		
		// out-parameters to lhs of call assignment
		int i = 0;
		for (VarList outVarList : calledProcedure.getOutParams()) {
			for (String oudVarId : outVarList.getIdentifiers()) {
				assert i < lhs.length : "missing left hand side for out-parameter";
				mapOutToLhs.put(oudVarId, lhs[i].getIdentifier());
				++i;
			}
		}
		assert i == lhs.length : "missing out-parameter for left hand side";
		return mapOutToLhs;
	}
	
}
