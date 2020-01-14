package de.uni_frieburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;

public class ReqTestResultUtil {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IReqSymbolTable mReqSymbolTable;

	public ReqTestResultUtil(final ILogger logger, final IUltimateServiceProvider services,
			final IReqSymbolTable reqSymbolTable) {
		mLogger = logger;
		mServices = services;
		mReqSymbolTable = reqSymbolTable;
	}

	public IResult convertTraceAbstractionResult(final IResult result) {
		if (result instanceof CounterExampleResult<?, ?, ?>) {
			return getTestSteps((CounterExampleResult<?, ?, ?>) result);
		} else if (result instanceof TimeoutResultAtElement<?>) {
			// TODO
		} else if (result instanceof PositiveResult<?>) {
			// TODO
		}
		return result;
	}

	private IResult getTestSteps(final CounterExampleResult<?, ?, ?> result) {
		final List<TestStep> testSteps = new ArrayList<>();
		@SuppressWarnings("unchecked")
		final IProgramExecution<?, Expression> translatedPe = (IProgramExecution<?, Expression>) mServices
				.getBacktranslationService().translateProgramExecution(result.getProgramExecution());

		// TODO get final element from result
		// final IElement checkedAnnotation = result.getElement();
		final AtomicTraceElement<?> finalElement = translatedPe.getTraceElement(translatedPe.getLength() - 1);
		for (int i = 0; i < translatedPe.getLength(); i++) {
			final AtomicTraceElement<?> ate = translatedPe.getTraceElement(i);
			if (ate.getStep() == finalElement.getStep()) {
				if (translatedPe.getProgramState(i) == null) {
					mLogger.warn(ate.getStep().toString());
					continue;
				}
				// TODO: filter for one state per loop
				final ProgramState<Expression> pgst = translatedPe.getProgramState(i);
				testSteps.add(getTestStep(pgst));
			}
		}
		return new ReqTestResultTest(testSteps);
	}

	private TestStep getTestStep(final ProgramState<Expression> programState) {
		final Map<IdentifierExpression, Collection<Expression>> inputAssignment = new HashMap<>();
		final Map<IdentifierExpression, Collection<Expression>> outputAssignment = new HashMap<>();
		Collection<Expression> waitForTime = new ArrayList<>();
		for (final Expression exp : programState.getVariables()) {
			if (exp instanceof IdentifierExpression
					&& mReqSymbolTable.getInputVars().contains(((IdentifierExpression) exp).getIdentifier())) {
				inputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			} else if (exp instanceof IdentifierExpression
					&& mReqSymbolTable.getDeltaVarName().equals(((IdentifierExpression) exp).getIdentifier())) {
				waitForTime = programState.getValues(exp);
			} else if (exp instanceof IdentifierExpression
					&& mReqSymbolTable.getOutputVars().contains(((IdentifierExpression) exp).getIdentifier())) {
				outputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			}

		}
		return new TestStep(inputAssignment, outputAssignment, waitForTime);
	}

	private String getTestAssertionName(final IElement e) {
		if (e instanceof AssertStatement) {
			final NamedAttribute[] attrs = ((AssertStatement) e).getAttributes();
			if (attrs != null && attrs.length > 0) {
				for (final NamedAttribute attr : attrs) {
					if (attr.getName().startsWith(ReqTestAnnotator.TEST_ASSERTION_PREFIX)) {
						return attr.getName();
					}
				}
			}
		}
		return "None";
	}

}
