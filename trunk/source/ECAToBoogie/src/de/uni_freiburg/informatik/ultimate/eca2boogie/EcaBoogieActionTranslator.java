package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.EcaStatus;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ContinuousForAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ContinuousUntilAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.DelayedAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.Duration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExactDurationValue;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.OnetimeAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.RecurringCountAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.RecurringUntilAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.RepeatAction;

/** Translates actions inline, sharing the rule's captured start time and allocating only the required fresh locals. */
public final class EcaBoogieActionTranslator {
	private final EcaBoogieSymbolTable mSymbols;
	private final EcaBoogieEventEncoding mEvents;
	private final VariableInfo mTime;

	public EcaBoogieActionTranslator(final EcaBoogieSymbolTable symbols, final EcaBoogieEventEncoding events,
			final VariableInfo time) {
		mSymbols = Objects.requireNonNull(symbols);
		mEvents = Objects.requireNonNull(events);
		mTime = Objects.requireNonNull(time);
		if (!BoogieType.TYPE_INT.equals(time.getType()) || symbols.lookupGlobal(time.getName()).orElse(null) != time) {
			throw new IllegalArgumentException("Actions require the registered global integer clock");
		}
	}

	public List<Statement> translate(final EcaAction action, final VariableInfo startTime,
			final EcaBoogieProcedureBuilder target) {
		if (target.getSymbolTable() != mSymbols || !BoogieType.TYPE_INT.equals(startTime.getType())
				|| mSymbols.lookupLocal(target.getProcedureId(), startTime.getName()).orElse(null) != startTime) {
			throw new IllegalArgumentException("Action and captured start time must belong to the rule procedure");
		}
		final Context context = new Context(action, startTime, target);
		return switch (action) {
		case final OnetimeAction ignored -> context.onetime();
		case final RepeatAction repeat -> context.repeat(repeat.getRepetitions());
		case final ContinuousUntilAction until -> context.continuousUntil(until.getUntilEvent());
		case final ContinuousForAction duration -> context.continuousFor(duration.getDuration());
		case final RecurringUntilAction recurring -> context.recurring(recurring.getPeriod(), recurring.getUntilEvent(), null);
		case final RecurringCountAction recurring -> context.recurring(recurring.getPeriod(), null, recurring.getRepetitions());
		case final DelayedAction delayed -> context.delayed(delayed.getDelay());
		};
	}

	private final class Context {
		private final EcaBoogieProcedureBuilder mTarget;
		private final ILocation mLocation;
		private final VariableInfo mStart;
		private final VariableInfo mStatus;
		private final VariableInfo mTimestamp;
		private final String mName;

		Context(final EcaAction action, final VariableInfo start, final EcaBoogieProcedureBuilder target) {
			mTarget = target;
			mLocation = action.getLocation() == null ? target.getLocation() : action.getLocation();
			mStart = start;
			mName = action.getActionId().getName();
			final InternalEventDeclaration declaration = mSymbols.lookupEventDeclaration(mName)
					.filter(InternalEventDeclaration.class::isInstance).map(InternalEventDeclaration.class::cast)
					.orElseThrow(() -> new IllegalArgumentException("Unknown internal action '" + mName + "'"));
			mStatus = mSymbols.getOrCreateActionStatus(declaration);
			mTimestamp = mSymbols.getOrCreateActionTimestamp(declaration);
		}

		List<Statement> onetime() {
			final List<Statement> block = new ArrayList<>();
			block.add(assume(binary(Operator.COMPEQ, ref(mTime), ref(mStart))));
			block.add(status(EcaStatus.DONE));
			block.addAll(occurrence());
			return List.of(atomic(block));
		}

		List<Statement> repeat(final BigInteger count) {
			positiveCount(count);
			final VariableInfo done = local("actionDone", BoogieType.TYPE_BOOL);
			final VariableInfo counter = local("repeatCount", BoogieType.TYPE_INT);
			final List<Statement> emit = new ArrayList<>(List.of(status(EcaStatus.ACTIVE_DONE),
					set(counter, binary(Operator.ARITHPLUS, ref(counter), integer(BigInteger.ONE)))));
			emit.addAll(occurrence());
			return List.of(atomic(List.of(set(done, bool(false)), set(counter, integer(BigInteger.ZERO)))),
					loop(not(ref(done)), atomic(List.of(when(binary(Operator.COMPGEQ, ref(counter), integer(count)),
							List.of(set(done, bool(true)), status(EcaStatus.DONE)), emit)))));
		}

		List<Statement> continuousUntil(final EcaEvent until) {
			final VariableInfo done = local("actionDone", BoogieType.TYPE_BOOL);
			final List<Statement> finish = new ArrayList<>(List.of(set(done, bool(true)), status(EcaStatus.DONE)));
			finish.addAll(occurrence());
			return List.of(atomic(List.of(assume(binary(Operator.COMPEQ, ref(mTime), ref(mStart))), set(done, bool(false)),
					activateContinuous())),
					loop(not(ref(done)), atomic(List.of(when(mEvents.condition(until), finish, List.of())))));
		}

		List<Statement> continuousFor(final Duration duration) {
			final VariableInfo active = local("actionActive", BoogieType.TYPE_BOOL);
			final VariableInfo deadline = local("deadline", BoogieType.TYPE_INT);
			final List<Statement> initialize = new ArrayList<>();
			final Expression delay = chooseDuration(duration, false, initialize);
			initialize.add(set(active, bool(true)));
			initialize.add(set(deadline, binary(Operator.ARITHPLUS, ref(mStart), delay)));
			initialize.add(activateContinuous());
			final List<Statement> finish = new ArrayList<>(List.of(set(active, bool(false)), status(EcaStatus.DONE)));
			finish.addAll(occurrence());
			return List.of(atomic(initialize), loop(ref(active), atomic(List.of(
					assume(binary(Operator.COMPLEQ, ref(mTime), ref(deadline))),
					when(binary(Operator.COMPLT, ref(mTime), ref(deadline)), List.of(), finish)))));
		}

		/** Shared recurring-until/count schedule; only the termination predicate and optional counter differ. */
		List<Statement> recurring(final Duration period, final EcaEvent until, final BigInteger count) {
			if (count != null) {
				positiveCount(count);
			}
			final VariableInfo done = local("actionDone", BoogieType.TYPE_BOOL);
			final VariableInfo deadline = local("deadline", BoogieType.TYPE_INT);
			final VariableInfo counter = count == null ? null : local("repeatCount", BoogieType.TYPE_INT);
			final List<Statement> initialize = new ArrayList<>(List.of(set(done, bool(false)), set(deadline, ref(mStart))));
			if (counter != null) {
				initialize.add(set(counter, integer(BigInteger.ZERO)));
			}
			final Expression stop = count == null ? mEvents.condition(until)
					: binary(Operator.COMPGEQ, ref(counter), integer(count));
			final List<Statement> emit = new ArrayList<>(List.of(status(EcaStatus.ACTIVE_DONE)));
			final Expression delay = chooseDuration(period, true, emit);
			emit.add(set(deadline, binary(Operator.ARITHPLUS, ref(deadline), delay)));
			if (counter != null) {
				emit.add(set(counter, binary(Operator.ARITHPLUS, ref(counter), integer(BigInteger.ONE))));
			}
			emit.addAll(occurrence());
			final Statement deadlineCheck = assume(binary(Operator.COMPLEQ, ref(mTime), ref(deadline)));
			return List.of(atomic(initialize), loop(not(ref(done)), atomic(List.of(deadlineCheck,
					when(stop, List.of(set(done, bool(true)), status(EcaStatus.DONE)),
							List.of(when(binary(Operator.COMPEQ, ref(mTime), ref(deadline)), emit, List.of())))))));
		}

		List<Statement> delayed(final Duration duration) {
			final EcaBoogieTimeEncoding.Bounds bounds = EcaBoogieTimeEncoding.bounds(duration, false);
			final Expression lower = binary(Operator.ARITHPLUS, ref(mStart), integer(bounds.lowerMillis()));
			final Expression upper = binary(Operator.ARITHPLUS, ref(mStart), integer(bounds.upperMillis()));
			final List<Statement> block = new ArrayList<>(List.of(assume(binary(Operator.LOGICAND,
					binary(Operator.COMPGEQ, ref(mTime), lower), binary(Operator.COMPLEQ, ref(mTime), upper))),
					status(EcaStatus.DONE)));
			block.addAll(occurrence());
			return List.of(atomic(block));
		}

		private Expression chooseDuration(final Duration duration, final boolean positive, final List<Statement> block) {
			final EcaBoogieTimeEncoding.Bounds bounds = EcaBoogieTimeEncoding.bounds(duration, positive);
			if (duration.getValue() instanceof ExactDurationValue) {
				return integer(bounds.lowerMillis());
			}
			final VariableInfo choice = local("durationChoice", BoogieType.TYPE_INT);
			block.add(mSymbols.havoc(choice, mLocation));
			block.add(assume(binary(Operator.LOGICAND, binary(Operator.COMPLEQ, integer(bounds.lower()), ref(choice)),
					binary(Operator.COMPLEQ, ref(choice), integer(bounds.upper())))));
			return binary(Operator.ARITHMUL, ref(choice), integer(bounds.unitMillis()));
		}

		private Statement activateContinuous() {
			// Called once per invocation: continued execution must not create completion history.
			return when(binary(Operator.COMPEQ, ref(mStatus), EcaBoogieStatusEncoding.literal(EcaStatus.PENDING, mLocation)),
					List.of(status(EcaStatus.ACTIVE)),
					List.of(when(binary(Operator.COMPEQ, ref(mStatus), EcaBoogieStatusEncoding.literal(EcaStatus.DONE, mLocation)),
							List.of(status(EcaStatus.ACTIVE_DONE)), List.of())));
		}

		private List<Statement> occurrence() {
			return List.of(mEvents.occurrenceStatement(mName, mLocation), set(mTimestamp, ref(mTime)));
		}

		private Statement status(final EcaStatus status) {
			return set(mStatus, EcaBoogieStatusEncoding.literal(status, mLocation));
		}

		private VariableInfo local(final String hint, final BoogieType type) {
			return mTarget.createAuxiliary(hint, type, mLocation);
		}

		private Expression ref(final VariableInfo variable) {
			return mSymbols.identifier(variable, mLocation);
		}

		private Expression integer(final BigInteger value) {
			return ExpressionFactory.createIntegerLiteral(mLocation, value.toString());
		}

		private Expression bool(final boolean value) {
			return ExpressionFactory.createBooleanLiteral(mLocation, value);
		}

		private Expression not(final Expression expression) {
			return ExpressionFactory.constructUnaryExpression(mLocation, UnaryExpression.Operator.LOGICNEG, expression);
		}

		private Expression binary(final Operator operator, final Expression left, final Expression right) {
			return ExpressionFactory.newBinaryExpression(mLocation, operator, left, right);
		}

		private Statement set(final VariableInfo variable, final Expression value) {
			return StatementFactory.constructSingleAssignmentStatement(mLocation, mSymbols.lhs(variable, mLocation), value);
		}

		private Statement assume(final Expression expression) {
			return new AssumeStatement(mLocation, expression);
		}

		private Statement atomic(final List<Statement> statements) {
			return StatementFactory.constructAtomicStatement(mLocation, statements);
		}

		private Statement when(final Expression condition, final List<Statement> thenPart, final List<Statement> elsePart) {
			return StatementFactory.constructIfStatement(mLocation, condition, thenPart.toArray(Statement[]::new),
					elsePart.toArray(Statement[]::new));
		}

		private Statement loop(final Expression condition, final Statement body) {
			return new WhileStatement(mLocation, condition, new LoopInvariantSpecification[0], new Statement[] { body });
		}
	}

	private static void positiveCount(final BigInteger count) {
		if (count.signum() <= 0) {
			throw new IllegalArgumentException("repeat count must be positive");
		}
	}
}
