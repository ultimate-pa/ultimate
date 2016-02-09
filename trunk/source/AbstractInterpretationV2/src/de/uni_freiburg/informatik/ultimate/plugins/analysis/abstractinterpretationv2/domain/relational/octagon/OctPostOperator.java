package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.BoogieUtil;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

public class OctPostOperator implements IAbstractPostOperator<OctDomainState, CodeBlock, IBoogieVar> {

	public OctDomainState join(List<OctDomainState> states) {
		OctDomainState joinedState = null;
		for (OctDomainState result : states) {
			if (joinedState == null) {
				joinedState = result;
			} else {
				joinedState = joinedState.join(result);
			}
		}
		return joinedState;
	}

	public List<OctDomainState> deepCopy(List<OctDomainState> states) {
		List<OctDomainState> copy = new ArrayList<>(states.size());
		states.forEach(state -> copy.add(state.deepCopy()));
		return copy; 
	}

	public List<OctDomainState> splitF(List<OctDomainState> oldStates,
			Function<List<OctDomainState>, List<OctDomainState>> op1,
			Function<List<OctDomainState>, List<OctDomainState>> op2) {

		List<OctDomainState> newStates = op1.apply(deepCopy(oldStates));
		newStates.addAll(op2.apply(oldStates));
		return joinIfGeMaxParallelStates(newStates);
	}

	public List<OctDomainState> splitC(List<OctDomainState> oldStates,
			Consumer<OctDomainState> op1, Consumer<OctDomainState> op2) {

		List<OctDomainState> copiedOldStates = deepCopy(oldStates);
		oldStates.forEach(op1);
		copiedOldStates.forEach(op2);
		oldStates.addAll(copiedOldStates);
		return joinIfGeMaxParallelStates(oldStates);
	}

	public static List<OctDomainState> removeBottomStates(List<OctDomainState> states) {
		List<OctDomainState> nonBottomStates = new ArrayList<>(states.size());
		for (OctDomainState state : states) {
			if (!state.isBottom()) {
				nonBottomStates.add(state);
			}
		}
		return nonBottomStates;
	}

	public List<OctDomainState> joinIfGeMaxParallelStates(List<OctDomainState> states) {
		states = removeBottomStates(states);
		if (states.isEmpty() || states.size() <= mMaxParallelStates) {
			return states;
		}
		List<OctDomainState> joinedStates = new ArrayList<>();
		joinedStates.add(join(states));
		return joinedStates;
	}
	
	public Logger getLogger() {
		return mLogger;
	}
	
	public ExpressionTransformer getExprTransformer() {
		return mExprTransformer;
	}
	
	public boolean isFallbackAssignIntervalProjectionEnabled() {
		return mFallbackAssignIntervalProjection;
	}

	////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

	private final Logger mLogger;
	private final BoogieSymbolTable mSymbolTable;
	private final int mMaxParallelStates;
	private final HavocBundler mHavocBundler;
	private final ExpressionTransformer mExprTransformer;
	private final OctStatementProcessor mStatementProcessor;
	private final boolean mFallbackAssignIntervalProjection;

	public OctPostOperator(Logger logger, BoogieSymbolTable symbolTable, int statesUntilMerge,
			boolean fallbackAssignIntervalProjection) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mMaxParallelStates = statesUntilMerge;
		mHavocBundler = new HavocBundler();
		mExprTransformer = new ExpressionTransformer();
		mStatementProcessor = new OctStatementProcessor(this);
		mFallbackAssignIntervalProjection = fallbackAssignIntervalProjection;
	}

	@Override
	public List<OctDomainState> apply(OctDomainState oldState, CodeBlock codeBlock) {
		List<OctDomainState> currentState = deepCopy(Collections.singletonList(oldState));
		List<Statement> statements = mHavocBundler.bundleHavocsCached(codeBlock);
		for (Statement statement : statements) {
			currentState = mStatementProcessor.processStatement(statement, currentState);
//			mLogger.warn("after " + BoogiePrettyPrinter.print(statement));
//			mLogger.warn(statement);
//			mLogger.warn(currentState);
//			mLogger.warn("---´");
		}
		currentState.forEach(s -> s.lock());
		return currentState;
	}

	@Override
	public List<OctDomainState> apply(
			OctDomainState stateBeforeTransition, OctDomainState stateAfterTransition, CodeBlock transition) {

		List<OctDomainState> result;
		if (transition instanceof Call) {
			result = applyCall(stateBeforeTransition, stateAfterTransition, (Call) transition);
		} else if (transition instanceof Return) {
			result = applyReturn(stateBeforeTransition, stateAfterTransition, (Return) transition);
		} else {
			throw new UnsupportedOperationException("Unsupported transition: " + transition);
		}
		result.forEach(s -> s.lock());
		return result;
	}
	
	private List<OctDomainState> applyCall(
			OctDomainState stateBeforeCall, OctDomainState stateAfterCall, Call callTransition) {

		if (stateAfterCall.isBottom()) {
			return new ArrayList<>();
		}

		CallStatement call = callTransition.getCallStatement();
		Procedure procedure = calledProcedure(call);

		Map<String, IBoogieVar> tmpVars = new HashMap<>();
		Map<String, String> mapTmpVarToInParam = new HashMap<>();
		Map<String, Expression> mapTmpVarToArg = new HashMap<>();
		int paramNumber = 0;
		for (VarList inParamList : procedure.getInParams()) {
			IType type = inParamList.getType().getBoogieType();
			if (!TypeUtil.isBoolean(type) && !TypeUtil.isNumeric(type)) {
				paramNumber += inParamList.getIdentifiers().length;
				continue;
				// results in "var := \top" for these variables, which is always assumed for unsupported types
			}
			for (String inParam : inParamList.getIdentifiers()) {
				String tmpVar = "octTmp(" + inParam + ")";
				IBoogieVar tmpBoogieVar = BoogieUtil.createTemporaryIBoogieVar(tmpVar, type);
				Expression arg = call.getArguments()[paramNumber];
				++paramNumber;

				tmpVars.put(tmpVar, tmpBoogieVar);
				mapTmpVarToInParam.put(tmpVar, inParam);
				
				mapTmpVarToArg.put(tmpVar, arg); // nothing will be overwritten -- in-parameters have unique names
			}
		}
		// add temporary variables
		List<OctDomainState> tmpStates = new ArrayList<>();
		tmpStates.add(stateBeforeCall.addVariables(tmpVars));

		// assign tmp := args
		tmpStates = deepCopy(tmpStates);
		for (Map.Entry<String, Expression> assign : mapTmpVarToArg.entrySet()) {
			tmpStates = mStatementProcessor.processSingleAssignment(assign.getKey(), assign.getValue(), tmpStates);
		}
		
		// copy to scope opened by call (inParam := tmp)
		// bottom-states are not overwritten (see top of this method)
		List<OctDomainState> result = new ArrayList<>();
		tmpStates.forEach(s -> result.add(stateAfterCall.copyValuesOnScopeChange(s, mapTmpVarToInParam)));
		return result;
		// No need to remove the temporary variables.
		// The states with temporary variables are only local variables of this method.
	}
	
	private List<OctDomainState> applyReturn(
			OctDomainState stateBeforeReturn, OctDomainState stateAfterReturn, Return returnTransition) {

		ArrayList<OctDomainState> result = new ArrayList<>();
		if (!stateAfterReturn.isBottom()) {
			CallStatement call = returnTransition.getCallStatement();
			Procedure procedure = calledProcedure(call);
			Map<String, String> mapOutToLhs = generateMapOutToLhs(call.getLhs(), procedure);
			stateAfterReturn = stateAfterReturn.copyValuesOnScopeChange(stateBeforeReturn, mapOutToLhs);
			result.add(stateAfterReturn);
		}
		return result;
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
			for (String outParam : outParamList.getIdentifiers()) {
				assert i < lhs.length : "missing left hand side for out-parameter";
				mapOutToLhs.put(outParam, lhs[i].getIdentifier());
				++i;
			}
		}
		assert i == lhs.length : "missing out-parameter for left hand side";
		return mapOutToLhs;
	}
	
}
