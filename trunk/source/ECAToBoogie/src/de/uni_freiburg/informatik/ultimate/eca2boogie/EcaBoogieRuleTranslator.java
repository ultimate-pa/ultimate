package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.AtomicRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.CompositeRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaRule;

/**
 * Translates the parser's rule tree into parameterless procedures. A false atomic condition skips the action and starts
 * the next loop iteration. Conditions are reused verbatim; actions share the rule's start time through inline
 * translation.
 */
public final class EcaBoogieRuleTranslator {
	private final EcaBoogieSymbolTable mSymbols;
	private final EcaBoogieEventEncoding mEvents;
	private final VariableInfo mTime;
	private int mNextRule;
	private int mNextThread = 1;

	public EcaBoogieRuleTranslator(final EcaBoogieSymbolTable symbols, final EcaBoogieEventEncoding events,
			final VariableInfo time) {
		mSymbols = Objects.requireNonNull(symbols);
		mEvents = Objects.requireNonNull(events);
		mTime = Objects.requireNonNull(time);
		if (!BoogieType.TYPE_INT.equals(time.getType()) || symbols.lookupGlobal(time.getName()).orElse(null) != time) {
			throw new IllegalArgumentException("The rule clock must be a registered global integer");
		}
	}

	/** Builds the rule procedures and returns one fork per top-level rule, to execute once after initialization. */
	public List<Statement> translateAndFork(final List<EcaRule> rules) {
		final List<Statement> forks = new ArrayList<>();
		for (final EcaRule rule : List.copyOf(rules)) {
			final String id = buildRule(rule);
			forks.add(fork(id, EcaBoogieSymbolTable.sourceOrDefault(rule.getLocation())));
		}
		return List.copyOf(forks);
	}

	private String buildRule(final EcaRule rule) {
		final String id = "eca$rule$" + mNextRule++;
		mSymbols.registerRuleProcedure(rule, id);
		final ILocation location = EcaBoogieSymbolTable.sourceOrDefault(rule.getLocation());
		final EcaBoogieProcedureBuilder target = new EcaBoogieProcedureBuilder(id, mSymbols, location);
		switch (rule) {
		case final AtomicRule atomic -> buildAtomicRule(atomic, target);
		case final CompositeRule composite -> {
			final List<String> children = Arrays.stream(composite.getChildRules()).map(this::buildRule).toList();
			if (children.isEmpty()) {
				throw new IllegalArgumentException("A composite ECA rule must have children");
			}
			switch (composite.getRuleType()) {
			case SEQUENTIAL -> children.forEach(child -> target.addStatement(call(child, location)));
			case PARALLEL -> children.forEach(child -> target.addStatement(fork(child, location)));
			case ROR -> target.addStatement(choice(children, 0, location));
			}
		}
		}
		target.build();
		return id;
	}

	private void buildAtomicRule(final AtomicRule rule, final EcaBoogieProcedureBuilder target) {
		final ILocation location = target.getLocation();
		// Fresh locals cannot shadow a source variable or action referenced by the unchanged condition expression.
		final VariableInfo seen = target.createAuxiliary("eventSeen", BoogieType.TYPE_BOOL, location);
		final VariableInfo startTime = target.createAuxiliary("startTime", BoogieType.TYPE_INT, location);
		final VariableInfo conditionHolds = target.createAuxiliary("conditionHolds", BoogieType.TYPE_BOOL, location);
		final List<Statement> iteration = new ArrayList<>();
		iteration.add(assign(seen, ExpressionFactory.createBooleanLiteral(location, false), location));
		iteration.add(waitForEvent(rule, seen, startTime, conditionHolds, location));
		final List<Statement> action =
				new EcaBoogieActionTranslator(mSymbols, mEvents, mTime).translate(rule.getAction(), startTime, target);
		iteration.add(StatementFactory.constructIfStatement(location, mSymbols.identifier(conditionHolds, location),
				action.toArray(Statement[]::new), new Statement[0]));
		target.addStatement(loop(ExpressionFactory.createBooleanLiteral(location, true), iteration, location));
	}

	private Statement waitForEvent(final AtomicRule rule, final VariableInfo seen, final VariableInfo startTime,
			final VariableInfo conditionHolds, final ILocation location) {
		final Statement observe = StatementFactory.constructIfStatement(location, mEvents.condition(rule.getEvent()),
				new Statement[] { assign(seen, ExpressionFactory.createBooleanLiteral(location, true), location),
						assign(startTime, mSymbols.identifier(mTime, location), location),
						assign(conditionHolds, rule.getCondition(), location) },
				new Statement[0]);
		return loop(negate(mSymbols.identifier(seen, location), location),
				List.of(StatementFactory.constructAtomicStatement(location, List.of(observe))), location);
	}

	private Statement choice(final List<String> children, final int index, final ILocation location) {
		if (index == children.size() - 1) {
			return call(children.get(index), location);
		}
		return StatementFactory.constructIfStatement(location,
				ExpressionFactory.constructBooleanWildCardExpression(location),
				new Statement[] { call(children.get(index), location) },
				new Statement[] { choice(children, index + 1, location) });
	}

	private Statement call(final String id, final ILocation location) {
		return StatementFactory.constructCallStatement(location, false, new VariableLHS[0], id, new Expression[0]);
	}

	private ForkStatement fork(final String id, final ILocation location) {
		return new ForkStatement(location,
				new Expression[] { ExpressionFactory.createIntegerLiteral(location, Integer.toString(mNextThread++)) },
				id, new Expression[0]);
	}

	private Statement assign(final VariableInfo variable, final Expression value, final ILocation location) {
		return StatementFactory.constructSingleAssignmentStatement(location, mSymbols.lhs(variable, location), value);
	}

	private static UnaryExpression negate(final Expression expression, final ILocation location) {
		// Retain an explicit negation for event-wait guards, including constant guards.
		return new UnaryExpression(location, BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG, expression);
	}

	private static WhileStatement loop(final Expression condition, final List<Statement> body,
			final ILocation location) {
		return new WhileStatement(location, condition, new LoopInvariantSpecification[0],
				body.toArray(Statement[]::new));
	}
}
