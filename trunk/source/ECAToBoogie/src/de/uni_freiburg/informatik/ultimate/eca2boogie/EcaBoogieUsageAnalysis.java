package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.eca.parser.EcaStatus;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.AtomicRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.CompositeRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ContinuousUntilAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.RecurringUntilAction;

/**
 * Extract and store names used in the ECA rules categorizing them into action names, condition names, and event names.
 */
final class EcaBoogieUsageAnalysis extends BoogieVisitor {
	private final Set<String> mConditions = new LinkedHashSet<>();
	private final Set<String> mEvents = new LinkedHashSet<>();
	private final Set<String> mActions = new LinkedHashSet<>();

	static EcaBoogieUsageAnalysis analyze(final EcaFile file) {
		final EcaBoogieUsageAnalysis usage = new EcaBoogieUsageAnalysis();
		file.getRules().forEach(usage::rule);
		return usage;
	}

	Set<String> conditionNames() {
		return Set.copyOf(mConditions);
	}

	Set<String> eventNames() {
		return Set.copyOf(mEvents);
	}

	Set<String> actionNames() {
		return Set.copyOf(mActions);
	}

	private void rule(final EcaRule rule) {
		if (rule instanceof final CompositeRule composite) {
			for (final EcaRule child : composite.getChildRules()) {
				rule(child);
			}
			return;
		}
		final AtomicRule atomic = (AtomicRule) rule;
		event(atomic.getEvent());
		condition(atomic.getCondition());
		final EcaAction action = atomic.getAction();
		mActions.add(action.getActionId().getName());
		mEvents.add(action.getActionId().getName());
		if (action instanceof final ContinuousUntilAction until) {
			event(until.getUntilEvent());
		} else if (action instanceof final RecurringUntilAction until) {
			event(until.getUntilEvent());
		}
	}

	private void event(final EcaEvent event) {
		if (event instanceof final InternalEvent internal) {
			mEvents.add(internal.getActionId().getName());
		} else if (event instanceof final ExternalEvent external) {
			mEvents.add(external.getActionId().getName());
		}
	}

	private void condition(final Expression expression) {
		processExpression(expression);
	}

	@Override
	protected void visit(final IdentifierExpression expression) {
		if (!EcaStatus.isLiteral(expression.getIdentifier())) {
			mConditions.add(expression.getIdentifier());
		}
	}
}
