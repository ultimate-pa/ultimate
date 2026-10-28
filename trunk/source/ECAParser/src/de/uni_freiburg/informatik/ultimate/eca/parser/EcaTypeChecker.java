package de.uni_freiburg.informatik.ultimate.eca.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.ITypeErrorReporter;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.TypeCheckHelper;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.AtomicRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.BooleanDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.CompositeRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ContinuousUntilAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.Declaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExternalEventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.FalseEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.IntegerDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.RecurringUntilAction;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.TrueExternalEvent;

/**
 * A small type checker for the eca language which is applied on an EcaFile after parsing. Rejects duplicate
 * declarations, checks that named events have the required internal or external kind and that actions refer to declared
 * internal events. Conditions must be Boolean, variables and event occurrences are typed using their declarations,
 * Boogie's type-checking helpers check the permitted expressions.
 */
public final class EcaTypeChecker {
	public record Diagnostic(ILocation location, String message) {
		@Override
		public String toString() {
			if (location == null) {
				return message;
			}
			return location.getFileName() + ":" + location.getStartLine() + ": " + message;
		}
	}

	private final Map<String, Declaration> mDeclarations = new HashMap<>();
	private final List<Diagnostic> mDiagnostics = new ArrayList<>();

	public List<Diagnostic> check(final EcaFile file) {
		Objects.requireNonNull(file);
		mDeclarations.clear();
		mDiagnostics.clear();
		for (final Declaration declaration : file.getDeclarations()) {
			// Store declarations in a symbol table and throw type error if there are duplicate declarations
			final String name = declaration.getName();
			final Declaration previous = mDeclarations.putIfAbsent(name, declaration);
			if (previous != null) {
				error(declaration.getLocation(), "Duplicate declaration of '" + name + "'");
			}
		}
		for (final EcaRule rule : file.getRules()) {
			// Check each rule
			checkRule(rule);
		}
		return List.copyOf(mDiagnostics);
	}

	private void checkRule(final EcaRule rule) {
		switch (rule) {
		case final CompositeRule composite -> {
			for (final EcaRule child : composite.getChildRules()) {
				// If all child rules are correctly typed, the composite rule is correctly typed
				checkRule(child);
			}
		}
		case final AtomicRule atomic -> {
			// In atomic rules event, condition, and action must be correctly typed
			checkEvent(atomic.getEvent(), false);
			checkAction(atomic.getAction());
			final BoogieType conditionType = typeOf(atomic.getCondition());
			if (!BoogieType.TYPE_ERROR.equals(conditionType) && !BoogieType.TYPE_BOOL.equals(conditionType)) {
				// Conditions must be boolean expressions
				error(atomic.getCondition().getLocation(),
						"Condition '" + BoogiePrettyPrinter.print(atomic.getCondition())
								+ "' must have Boolean type, but has type " + conditionType);
			}
		}
		}
	}

	private void checkAction(final EcaAction action) {
		final String name = action.getActionId().getName();
		if (!(mDeclarations.get(name) instanceof InternalEventDeclaration)) {
			// Actions must be internal events
			error(action.getActionId().getLocation(), "Action '" + name + "' must name a declared internal event");
		}
		if (action instanceof final ContinuousUntilAction continuous) {
			checkEvent(continuous.getUntilEvent(), true);
		} else if (action instanceof final RecurringUntilAction recurring) {
			checkEvent(recurring.getUntilEvent(), true);
		}
	}

	private void checkEvent(final EcaEvent event, final boolean terminationEvent) {
		if (event instanceof final InternalEvent internal) {
			checkNamedEvent(internal.getActionId().getName(), InternalEventDeclaration.class, event.getLocation());
		} else if (event instanceof final ExternalEvent external) {
			checkNamedEvent(external.getActionId().getName(), ExternalEventDeclaration.class, event.getLocation());
		} else if (event instanceof FalseEvent && !terminationEvent) {
			// False events are only permitted in until to model non-terminating continuous actions
			error(event.getLocation(), "false is only permitted as an until event");
		} else if (!(event instanceof TrueExternalEvent) && !(event instanceof FalseEvent)) {
			error(event.getLocation(), "Unsupported ECA event");
		}
	}

	private void checkNamedEvent(final String name, final Class<? extends EventDeclaration> expectedKind,
			final ILocation location) {
		final Declaration declaration = mDeclarations.get(name);
		if (!expectedKind.isInstance(declaration)) {
			final String kind = expectedKind == InternalEventDeclaration.class ? "intern" : "extern";
			error(location, "Event '" + name + "' must be declared " + kind);
		}
	}

	private BoogieType typeOf(final Expression expression) {
		final BoogieType type;
		switch (expression) {
		case final IntegerLiteral ignored -> type = BoogieType.TYPE_INT;
		case final BooleanLiteral ignored -> type = BoogieType.TYPE_BOOL;
		case final IdentifierExpression identifier -> type = typeOfIdentifier(identifier);
		case final UnaryExpression unary -> type = typeOfUnary(unary);
		case final BinaryExpression binary -> type = typeOfBinary(binary);
		default -> {
			error(expression.getLocation(), "Expression form is not allowed in ECA conditions");
			type = BoogieType.TYPE_ERROR;
		}
		}
		expression.setType(type);
		return type;
	}

	private BoogieType typeOfIdentifier(final IdentifierExpression identifier) {
		final String name = identifier.getIdentifier();
		return switch (mDeclarations.get(name)) {
		case final IntegerDeclaration ignored -> BoogieType.TYPE_INT;
		case final BooleanDeclaration ignored -> BoogieType.TYPE_BOOL;
		case final EventDeclaration ignored -> BoogieType.TYPE_BOOL; // True if the event has occurred, false otherwise
		case null -> {
			error(identifier.getLocation(), "Undeclared identifier '" + name + "' in condition");
			yield BoogieType.TYPE_ERROR;
		}
		default -> {
			error(identifier.getLocation(), "Identifier '" + name + "' cannot be used in a condition");
			yield BoogieType.TYPE_ERROR;
		}
		};
	}

	private BoogieType typeOfUnary(final UnaryExpression unary) {
		final BoogieType operandType = typeOf(unary.getExpr());
		if (unary.getOperator() != UnaryExpression.Operator.LOGICNEG) {
			// Negation is the only unary operator
			error(unary.getLocation(), "Unary operator is not allowed in ECA conditions");
			return BoogieType.TYPE_ERROR;
		}
		final int previousErrors = mDiagnostics.size();
		final BoogieType result = TypeCheckHelper.typeCheckUnaryExpression(unary.getOperator(), operandType,
				reporter(unary, operandType));
		return BoogieType.TYPE_ERROR.equals(operandType) || mDiagnostics.size() != previousErrors
				? BoogieType.TYPE_ERROR
				: result;
	}

	private BoogieType typeOfBinary(final BinaryExpression binary) {
		final BoogieType leftType = typeOf(binary.getLeft());
		final BoogieType rightType = typeOf(binary.getRight());
		if (!isAllowedBinOp(binary.getOperator())) {
			error(binary.getLocation(), "Binary operator is not allowed in ECA conditions");
			return BoogieType.TYPE_ERROR;
		}
		if (binary.getOperator() == BinaryExpression.Operator.ARITHMUL && !(binary.getLeft() instanceof IntegerLiteral)
				&& !(binary.getRight() instanceof IntegerLiteral)) {
			// One side of the multiplication must be an integer constant
			error(binary.getLocation(), "Multiplication requires an integer literal operand");
			return BoogieType.TYPE_ERROR;
		}
		final int previousErrors = mDiagnostics.size();
		final BoogieType result = TypeCheckHelper.typeCheckBinaryExpression(binary.getOperator(), leftType, rightType,
				reporter(binary, leftType, rightType));
		return BoogieType.TYPE_ERROR.equals(leftType) || BoogieType.TYPE_ERROR.equals(rightType)
				|| mDiagnostics.size() != previousErrors ? BoogieType.TYPE_ERROR : result;
	}

	private static boolean isAllowedBinOp(final BinaryExpression.Operator operator) {
		return switch (operator) {
		case LOGICIMPLIES, LOGICAND, LOGICOR, COMPLT, COMPGT, COMPLEQ, COMPGEQ, COMPEQ, COMPNEQ, ARITHPLUS, ARITHMINUS,
				ARITHMUL -> true;
		default -> false;
		};
	}

	private ITypeErrorReporter<String> reporter(final UnaryExpression unary, final BoogieType operandType) {
		return ignored -> error(unary.getLocation(),
				"Operator '!' requires a Boolean operand in '" + BoogiePrettyPrinter.print(unary) + "', but '"
						+ BoogiePrettyPrinter.print(unary.getExpr()) + "' has type " + operandType);
	}

	private ITypeErrorReporter<String> reporter(final BinaryExpression binary, final BoogieType leftType,
			final BoogieType rightType) {
		return ignored -> {
			final String operator;
			final String requiredTypes;
			switch (binary.getOperator()) {
			case ARITHPLUS -> {
				operator = "+";
				requiredTypes = "integer operands";
			}
			case ARITHMINUS -> {
				operator = "-";
				requiredTypes = "integer operands";
			}
			case ARITHMUL -> {
				operator = "*";
				requiredTypes = "integer operands";
			}
			case COMPLT -> {
				operator = "<";
				requiredTypes = "integer operands";
			}
			case COMPGT -> {
				operator = ">";
				requiredTypes = "integer operands";
			}
			case COMPLEQ -> {
				operator = "<=";
				requiredTypes = "integer operands";
			}
			case COMPGEQ -> {
				operator = ">=";
				requiredTypes = "integer operands";
			}
			case LOGICAND -> {
				operator = "&&";
				requiredTypes = "Boolean operands";
			}
			case LOGICOR -> {
				operator = "||";
				requiredTypes = "Boolean operands";
			}
			case LOGICIMPLIES -> {
				operator = "==>";
				requiredTypes = "Boolean operands";
			}
			case COMPEQ -> {
				operator = "==";
				requiredTypes = "operands of the same type (both integer or both Boolean)";
			}
			case COMPNEQ -> {
				operator = "!=";
				requiredTypes = "operands of the same type (both integer or both Boolean)";
			}
			default -> throw new IllegalStateException("Unexpected ECA operator: " + binary.getOperator());
			}
			error(binary.getLocation(), "Operator '" + operator + "' requires " + requiredTypes + " in '"
					+ BoogiePrettyPrinter.print(binary) + "', but left operand '"
					+ BoogiePrettyPrinter.print(binary.getLeft()) + "' has type " + leftType + " and right operand '"
					+ BoogiePrettyPrinter.print(binary.getRight()) + "' has type " + rightType);
		};
	}

	private void error(final ILocation location, final String message) {
		mDiagnostics.add(new Diagnostic(location, message));
	}
}
