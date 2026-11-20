package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExternalEventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.FalseEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.TrueExternalEvent;

/**
 * Encodes the fact that an event has occurred using a separate global Boolean flag, never its action-status variable.
 * Explicit initialization
 * starts a new history with all flags false. Internal occurrences set their flag true; external sampling may set an
 * external flag true. Neither operation resets history. The caller decides when initialization and sampling occur.
 * Original ECA condition expressions are not rewritten.
 */
public final class EcaBoogieEventEncoding {
	public record EventDescriptor(EventDeclaration declaration, VariableInfo variable) {
		public EventDescriptor {
			Objects.requireNonNull(declaration);
			Objects.requireNonNull(variable);
		}

		public boolean isExternal() {
			return declaration instanceof ExternalEventDeclaration;
		}
	}

	private final EcaBoogieSymbolTable mSymbols;
	private final Map<String, EventDescriptor> mEvents = new LinkedHashMap<>();

	public EcaBoogieEventEncoding(final EcaBoogieSymbolTable symbols, final EcaFile file) {
		this(symbols, Objects.requireNonNull(file).getDeclarations().stream().filter(EventDeclaration.class::isInstance)
				.map(EventDeclaration.class::cast).toList());
	}

	/** Reuses registered event variables and registers missing events. Duplicate ECA event declarations are rejected. */
	public EcaBoogieEventEncoding(final EcaBoogieSymbolTable symbols,
			final Collection<? extends EventDeclaration> declarations) {
		mSymbols = Objects.requireNonNull(symbols);
		final Map<String, EventDeclaration> byName = new LinkedHashMap<>();
		for (final EventDeclaration declaration : List.copyOf(declarations)) {
			final String name = Objects.requireNonNull(declaration.getName());
			if (name.isBlank() || byName.putIfAbsent(name, declaration) != null) {
				throw new IllegalArgumentException("Invalid or duplicate event declaration '" + name + "'");
			}
			if (symbols.lookupGlobal(name).isPresent() && symbols.lookupEventVariable(name).isEmpty()) {
				throw new IllegalArgumentException("Event '" + name + "' conflicts with an ordinary variable");
			}
			if (symbols.lookupEventVariable(name).isPresent()) {
				final boolean internal = !(declaration instanceof ExternalEventDeclaration);
				if (symbols.lookupActionStatusVariable(name).isPresent() != internal) {
					throw new IllegalArgumentException("Event kind does not match registered event '" + name + "'");
				}
			}
		}
		for (final EventDeclaration declaration : byName.values()) {
			final VariableInfo variable = symbols.lookupEventVariable(declaration.getName())
					.orElseGet(() -> symbols.registerEvent(declaration));
			mEvents.put(declaration.getName(), new EventDescriptor(declaration, variable));
		}
	}

	public Optional<EventDescriptor> lookup(final String eventName) {
		return Optional.ofNullable(mEvents.get(Objects.requireNonNull(eventName)));
	}

	public List<EventDescriptor> getEvents() {
		return List.copyOf(mEvents.values());
	}

	/** Builds a typed event guard, including constant true/false events, without changing existing conditions. */
	public Expression condition(final EcaEvent event) {
		Objects.requireNonNull(event);
		final ILocation location = EcaBoogieSymbolTable.sourceOrDefault(event.getLocation());
		return switch (event) {
		case final TrueExternalEvent ignored -> ExpressionFactory.createBooleanLiteral(location, true);
		case final FalseEvent ignored -> ExpressionFactory.createBooleanLiteral(location, false);
		case final InternalEvent internal -> namedCondition(internal.getActionId().getName(), false, location);
		case final ExternalEvent external -> namedCondition(external.getActionId().getName(), true, location);
		};
	}

	/** Initializes all event-history flags to false. This is intended to be called once at program startup. */
	public void addInitialization(final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		final List<Statement> statements = new ArrayList<>();
		for (final EventDescriptor event : mEvents.values()) {
			statements.add(assignment(event, false, target.getLocation()));
		}
		target.addStatements(statements);
	}

	/**
	 * Adds one sampling step: independently for each external event, a nondeterministic branch may set its flag true.
	 * Previously observed events remain true. Internal events are unaffected; no sampling schedule is imposed here.
	 */
	public void addExternalEventHandling(final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		final ILocation location = target.getLocation();
		final List<Statement> statements = new ArrayList<>();
		for (final EventDescriptor event : mEvents.values()) {
			if (event.isExternal()) {
				statements.add(StatementFactory.constructIfStatement(location,
						ExpressionFactory.constructBooleanWildCardExpression(location),
						new Statement[] { assignment(event, true, location) }, new Statement[0]));
			}
		}
		target.addStatements(statements);
	}

	/** Records an internal action event. External occurrences are supplied by addExternalEventHandling instead. */
	public void addEventOccurrence(final String eventName, final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		final EventDescriptor event = requireEvent(eventName);
		if (event.isExternal()) {
			throw new IllegalArgumentException("Action '" + eventName + "' must refer to an internal event");
		}
		target.addStatement(assignment(event, true, target.getLocation()));
	}

	private Expression namedCondition(final String name, final boolean external, final ILocation location) {
		final EventDescriptor event = requireEvent(name);
		if (event.isExternal() != external) {
			throw new IllegalArgumentException("Event '" + name + "' must be declared " + (external ? "extern" : "intern"));
		}
		return mSymbols.identifier(event.variable(), location);
	}

	private Statement assignment(final EventDescriptor event, final boolean value, final ILocation location) {
		return StatementFactory.constructSingleAssignmentStatement(location, mSymbols.lhs(event.variable(), location),
				ExpressionFactory.createBooleanLiteral(location, value));
	}

	private EventDescriptor requireEvent(final String name) {
		return lookup(name).orElseThrow(() -> new IllegalArgumentException("Unknown event '" + name + "'"));
	}

	private void checkTarget(final EcaBoogieProcedureBuilder target) {
		if (Objects.requireNonNull(target).getSymbolTable() != mSymbols) {
			throw new IllegalArgumentException("Event encoding and procedure builder must share one symbol table");
		}
	}
}
