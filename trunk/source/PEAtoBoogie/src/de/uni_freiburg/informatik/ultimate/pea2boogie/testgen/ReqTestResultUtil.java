package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.core.lib.results.CounterExampleResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TimeoutResultAtElement;
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
		final AtomicTraceElement<?> finalElement = translatedPe.getTraceElement(translatedPe.getLength() - 1);
		ProgramState<Expression> peek = null;
		for (int i = 0; i < translatedPe.getLength(); i++) {
			if (translatedPe.getProgramState(i) != null) {
				peek = translatedPe.getProgramState(i);
			}
			final AtomicTraceElement<?> ate = translatedPe.getTraceElement(i);
			if (ate.getStep() == finalElement.getStep()) {
				if (peek == null) {
					mLogger.error(
							"Assertion did not contain state (but would have been neccessary for test generation):"
									+ ate.getStep().toString());
					continue;
				}
				testSteps.add(getTestStep(peek));
				peek = null;
			}
		}
		return new ReqTestResultTest(testSteps, getTestAssertionName(finalElement.getStep()));
	}

	private TestStep getTestStep(final ProgramState<Expression> programState) {
		final Map<IdentifierExpression, Collection<Expression>> inputAssignment = new HashMap<>();
		final Map<IdentifierExpression, Collection<Expression>> outputAssignment = new HashMap<>();
		Collection<Expression> waitForTime = new ArrayList<>();
		for (final Expression exp : programState.getVariables()) {
			final String ident = ((IdentifierExpression) exp).getIdentifier();
			if (exp instanceof IdentifierExpression && mReqSymbolTable.getInputVars().contains(ident)) {
				inputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			} else if (exp instanceof IdentifierExpression && mReqSymbolTable.getDeltaVarName().equals(ident)) {
				waitForTime = programState.getValues(exp);
			} else if (exp instanceof IdentifierExpression && mReqSymbolTable.getOutputVars().contains(ident)
					&& isSetByEffect(ident, programState)) {
				outputAssignment.put((IdentifierExpression) exp, programState.getValues(exp));
			}

		}
		return new TestStep(inputAssignment, outputAssignment, waitForTime);
	}

	private boolean isSetByEffect(final String ident, final ProgramState<Expression> programState) {
		final String trackingVar = ReqTestAnnotator.getTrackingVar(ident);
		for (final Expression identExpr : programState.getVariables()) {
			if (((IdentifierExpression) identExpr).getIdentifier().equals(trackingVar)) {
				for (final Expression expr : programState.getValues(identExpr)) {
					if (expr instanceof BooleanLiteral) {
						return ((BooleanLiteral) expr).getValue();
					}
					mLogger.error("Unsuspected Value for tracking Variable for var: " + ident);
				}
			}
		}
		return false;
	}

	private static String getTestAssertionName(final Object e) {
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
