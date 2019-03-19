package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.StepInfo;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.GraphToBoogie;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphOracleAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class CounterExampleToTest {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ReqSymbolTable mReqSymbolTable;
	private final AuxVarGen mAuxVarGen;
	
	public CounterExampleToTest(ILogger logger, IUltimateServiceProvider services, ReqSymbolTable reqSymbolTable, 
			AuxVarGen auxVarGen) {
		mLogger = logger;
		mServices = services;
		mReqSymbolTable = reqSymbolTable;
		mAuxVarGen = auxVarGen;
		
	}
	
	public IResult convertCounterExampleToTest(final IResult result) {
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			return transformCounterExampleToExecutionSteps((CounterExampleResult<?, ?, ?>)result);
		} else if (result instanceof TimeoutResultAtElement<?>){	
			return transformTimeOutResult((TimeoutResultAtElement<?>) result);
		} else if (result instanceof PositiveResult<?>) {
			return transformPositiveResult((PositiveResult<?>) result);
		} else {
			return null;
		}
	}
	
	private IResult transformTimeOutResult(final TimeoutResultAtElement<?> result) {
		IElement element = result.getElement();
		if (ReqGraphOracleAnnotation.getAnnotation(element) != null) {
			ReqGraphOracleAnnotation oracle = ReqGraphOracleAnnotation.getAnnotation(element);
			String message = String.format("Found no Test for (TIMEOUT): %s (%s)", oracle.getOracleVars(), oracle.getRequirementAut().getName());
			return new GenericResult("TestGen",
					message,
					message, 
					IResultWithSeverity.Severity.WARNING );
		} else {
			return null;
		}
	}
	
	private IResult transformPositiveResult(final PositiveResult<?> result) {
		IElement element = result.getElement();
		if (ReqGraphOracleAnnotation.getAnnotation(element) != null) {
			ReqGraphOracleAnnotation oracle = ReqGraphOracleAnnotation.getAnnotation(element);
			String message = String.format("There is no test for (SAFE): %s (%s)", oracle.getOracleVars(), oracle.getRequirementAut().getName());
			return new GenericResult("TestGen",
					message,
					message, 
					IResultWithSeverity.Severity.WARNING );
		} else {
			return null;
		}
	}
	
	private IResult transformCounterExampleToExecutionSteps(final CounterExampleResult<?, ?, ?> result){
		IProgramExecution<?, ?> translatedPe = mServices.getBacktranslationService().translateProgramExecution(result.getProgramExecution());
		
		List<SystemState> systemStates = new ArrayList<>();
		List<List<ReqGraphAnnotation>> stepGuards = new ArrayList<>();
		List<ReqGraphAnnotation> stepGuard = new ArrayList<>();
		ReqGraphOracleAnnotation oracle = null;
		for(int i = 0; i < translatedPe.getLength(); i++) {
			AtomicTraceElement<IElement> ate = ((AtomicTraceElement<IElement>) translatedPe.getTraceElement(i));
			IElement element = ate.getTraceElement();
			// retrieve system state
			if( isTestPurposeAssertion(element)) {
				if (translatedPe.getProgramState(i) == null) {
					continue;
				}
				systemStates.add(generateSystemState((ProgramState<Expression>)translatedPe.getProgramState(i)));
				stepGuards.add(stepGuard);
				stepGuard = new ArrayList<>();
			} 
			// retrieve guardAnnotations of encoded automata
			if (ReqGraphAnnotation.getAnnotation(element) != null) {
					stepGuard.add( ReqGraphAnnotation.getAnnotation(element));
			}
			//retrieve oracle annotation (note: guard of the last assert statement)
			if (ReqGraphOracleAnnotation.getAnnotation(element) != null) {
				oracle = ReqGraphOracleAnnotation.getAnnotation(element);
			}
		}
		mLogger.warn("Oracle: " + oracle.getAnnotationsAsMap().toString());
		TestGeneratorResult testSequence = new TestGeneratorResult(mLogger, systemStates, stepGuards, oracle, mReqSymbolTable, mAuxVarGen);
		return testSequence;
	}
	
	private boolean isTestPurposeAssertion(final IElement e) {
		if (e instanceof AssertStatement) {
			NamedAttribute[] attrs = ((AssertStatement) e).getAttributes();
			if(attrs != null && attrs.length>0) {
				for(NamedAttribute attr: attrs) {
					if(attr.getName() == GraphToBoogie.TEST_ORACLE_MARKER) return true;
				}
			}
		}
		return false;
	}
	
	private SystemState generateSystemState(final ProgramState<Expression> programState) {
		LinkedHashMap<Expression, Collection<Expression>> observableState = new LinkedHashMap<>();
		LinkedHashSet<Expression> inputs = new LinkedHashSet<>();
		int i = 0;
		for(Expression e: programState.getVariables()) {
			if (e instanceof IdentifierExpression && 
				! mReqSymbolTable.isAuxVar(((IdentifierExpression) e).getIdentifier())) {	
					observableState.put(e, programState.getValues(e));
					inputs.add(e);
			}
			if (e instanceof IdentifierExpression && 
				((IdentifierExpression) e).getIdentifier().equals(GraphToBoogie.GLOBAL_CLOCK_VAR)){
				IntegerLiteral ilit = (IntegerLiteral) programState.getValues(e).toArray(new Expression[programState.getValues(e).size()])[0];
					i =  Integer.parseInt(ilit.getValue());
			}
		}
		return new SystemState(observableState, i);
	}
	
}























