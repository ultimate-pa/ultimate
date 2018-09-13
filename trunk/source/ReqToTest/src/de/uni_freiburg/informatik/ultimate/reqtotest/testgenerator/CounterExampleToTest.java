package de.uni_freiburg.informatik.ultimate.reqtotest.testgenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.GraphToBoogie;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;

public class CounterExampleToTest {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final ReqSymbolTable mReqSymbolTable;
	
	public CounterExampleToTest(ILogger logger, IUltimateServiceProvider services, ReqSymbolTable reqSymbolTable) {
		mLogger = logger;
		mServices = services;
		mReqSymbolTable = reqSymbolTable;
	}
	
	public IResult convertCounterExampleToTest(final IResult result) {
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			return generateTestSequence((CounterExampleResult<?, ?, ?>)result);
		} else {
			// report that no test is possible
			return null;
		}
	}
	
	private IResult generateTestSequence(final CounterExampleResult<?, ?, ?> result){
		IProgramExecution<IElement, Term> execution =  (IProgramExecution<IElement, Term>) result.getProgramExecution(); 
		IProgramExecution<?, ?> translatedPe = mServices.getBacktranslationService().translateProgramExecution(result.getProgramExecution());
		
		List<ProgramState<Expression>> systemStates = new ArrayList<>();
		for(int i = 0; i < translatedPe.getLength(); i++) {
			if( isTestPurposeAssertion((AtomicTraceElement<IElement>) translatedPe.getTraceElement(i))) {
				if (translatedPe.getProgramState(i) == null) continue;
				systemStates.add(generateObservableProgramState((ProgramState<Expression>)translatedPe.getProgramState(i)));
			}
		}
		TestGeneratorResult testSequence = new TestGeneratorResult(systemStates);
		return testSequence;
	}
	
	private boolean isTestPurposeAssertion(final AtomicTraceElement<IElement> atomicTraceElement) {
		IElement e = atomicTraceElement.getTraceElement();
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
	
	private ProgramState<Expression> generateObservableProgramState(final ProgramState<Expression> programState) {
		LinkedHashMap<Expression, Collection<Expression>> observableState = new LinkedHashMap<>();
		for(Expression e: programState.getVariables()) {
			mLogger.warn(e.toString() + "=" + programState.getValues(e).toString());
			if(e instanceof IdentifierExpression &&
					( mReqSymbolTable.containsInput(((IdentifierExpression) e).getIdentifier())
					|| (mReqSymbolTable.containsOutput(((IdentifierExpression) e).getIdentifier())
						&& isDefinedFlagSet(((IdentifierExpression) e).getIdentifier(), programState)))) {	
				observableState.put(e, programState.getValues(e));
			}
		}
		return new ProgramState<Expression>(observableState);
	}
	
	private boolean isDefinedFlagSet(String ident, ProgramState<Expression> state) {
		String useIdent = "u_" + ident;
		for(Expression e: state.getVariables()) {
			if(e instanceof IdentifierExpression && ((IdentifierExpression) e).getIdentifier().equals(useIdent)){
				Collection<Expression> values = state.getValues(e);
				for(Expression v: values) {
					return v instanceof BooleanLiteral && ((BooleanLiteral)v).getValue() == true;
				}
			}
				
		}
		return false;
	}
	
}























