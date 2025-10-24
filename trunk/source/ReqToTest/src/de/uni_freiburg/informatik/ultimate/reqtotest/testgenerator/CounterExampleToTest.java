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
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
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
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.AuxVarGen;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.GraphToBoogie;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.ReqGraphOracleAnnotation;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.Req2TestReqSymbolTable;

public class CounterExampleToTest {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final Req2TestReqSymbolTable mReqSymbolTable;
	private final AuxVarGen mAuxVarGen;

	public CounterExampleToTest(final ILogger logger, final IUltimateServiceProvider services,
			final Req2TestReqSymbolTable reqSymbolTable, final AuxVarGen auxVarGen) {
		mLogger = logger;
		mServices = services;
		mReqSymbolTable = reqSymbolTable;
		mAuxVarGen = auxVarGen;

	}

	public IResult convertCounterExampleToTest(final IResult result) {
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			return transformCounterExampleToExecutionSteps((CounterExampleResult<?, ?, ?>) result);
		} else if (result instanceof TimeoutResultAtElement<?>) {
			return transformTimeOutResult((TimeoutResultAtElement<?>) result);
		} else if (result instanceof PositiveResult<?>) {
			return transformPositiveResult((PositiveResult<?>) result);
		} else {
			return null;
		}
	}

	private IResult transformTimeOutResult(final TimeoutResultAtElement<?> result) {
		final IElement element = result.getElement();
		if (ReqGraphOracleAnnotation.getAnnotation(element) != null) {
			final ReqGraphOracleAnnotation oracle = ReqGraphOracleAnnotation.getAnnotation(element);
			final String message = String.format("Found no Test for (TIMEOUT): %s (%s)", oracle.getOracleVars(),
					oracle.getRequirementAut().getName());
			return new GenericResult("TestGen", message, message, IResultWithSeverity.Severity.WARNING);
		} else {
			return null;
		}
	}

	private IResult transformPositiveResult(final PositiveResult<?> result) {
		final IElement element = result.getElement();
		if (ReqGraphOracleAnnotation.getAnnotation(element) != null) {
			final ReqGraphOracleAnnotation oracle = ReqGraphOracleAnnotation.getAnnotation(element);
			final String message = String.format("There is no test for (SAFE): %s (%s)", oracle.getOracleVars(),
					oracle.getRequirementAut().getName());
			return new GenericResult("TestGen", message, message, IResultWithSeverity.Severity.WARNING);
		} else {
			return null;
		}
	}

	private IResult transformCounterExampleToExecutionSteps(final CounterExampleResult<?, ?, ?> result) {
		final IProgramExecution<?, ?> translatedPe =
				mServices.getBacktranslationService().translateProgramExecution(result.getProgramExecution());

		final List<SystemState> systemStates = new ArrayList<>();
		final List<List<ReqGraphAnnotation>> stepGuards = new ArrayList<>();
		List<ReqGraphAnnotation> stepGuard = new ArrayList<>();
		ReqGraphOracleAnnotation oracle = null;
		for (int i = 0; i < translatedPe.getLength(); i++) {
			final AtomicTraceElement<IElement> ate = ((AtomicTraceElement<IElement>) translatedPe.getTraceElement(i));
			final IElement element = ate.getTraceElement();
			// retrieve system state
			if (isTestPurposeAssertion(element)) {
				if (translatedPe.getProgramState(i) == null) {
					continue;
				}
				systemStates.add(generateSystemState((ProgramState<Expression>) translatedPe.getProgramState(i)));
				stepGuards.add(stepGuard);
				stepGuard = new ArrayList<>();
			}
			// retrieve guardAnnotations of encoded automata
			if (ReqGraphAnnotation.getAnnotation(element) != null) {
				stepGuard.add(ReqGraphAnnotation.getAnnotation(element));
			}
			// retrieve oracle annotation (note: guard of the last assert statement)
			if (ReqGraphOracleAnnotation.getAnnotation(element) != null) {
				oracle = ReqGraphOracleAnnotation.getAnnotation(element);
			}
		}
		mLogger.warn("Oracle: " + oracle.getAnnotationsAsMap().toString());
		final TestGeneratorResult testSequence =
				new TestGeneratorResult(mLogger, systemStates, stepGuards, oracle, mReqSymbolTable, mAuxVarGen);
		return testSequence;
	}

	private boolean isTestPurposeAssertion(final IElement e) {
		if (e instanceof AssertStatement) {
			final NamedAttribute[] attrs = ((AssertStatement) e).getAttributes();
			if (attrs != null && attrs.length > 0) {
				for (final NamedAttribute attr : attrs) {
					if (attr.getName() == GraphToBoogie.TEST_ORACLE_MARKER) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private SystemState generateSystemState(final ProgramState<Expression> programState) {
		final LinkedHashMap<Expression, Collection<Expression>> observableState = new LinkedHashMap<>();
		final LinkedHashSet<Expression> inputs = new LinkedHashSet<>();
		float i = 0;
		for (final Expression e : programState.getVariables()) {
			if (e instanceof IdentifierExpression
					&& !mReqSymbolTable.isAuxVar(((IdentifierExpression) e).getIdentifier())) {
				observableState.put(e, programState.getValues(e));
				inputs.add(e);
			}
			if (e instanceof IdentifierExpression
					&& ((IdentifierExpression) e).getIdentifier().equals(GraphToBoogie.GLOBAL_CLOCK_VAR)) {
				final Expression expr =
						programState.getValues(e).toArray(new Expression[programState.getValues(e).size()])[0];
				if (expr instanceof RealLiteral) {
					i = Float.parseFloat(((RealLiteral) expr).getValue());
				} else if (expr instanceof IntegerLiteral) {
					i = Float.parseFloat(((IntegerLiteral) expr).getValue());
				}
			}
		}
		return new SystemState(observableState, i);
	}

}
