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
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.TrueExternalEvent;

/**
 * Encodes the fact that an event has occurred using a separate global Boolean flag. Initialization sets all flags
 * false. At each time step external flags are sampled afresh and internal flags are reset; internal occurrences then
 * set their flag true. Status variables are never changed by this encoding. Original ECA condition expressions are not
 * rewritten.
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

	/** Registers the file's used variable roles, and encodes only its referenced/emitted occurrence flags. */
	public EcaBoogieEventEncoding(final EcaBoogieSymbolTable symbols, final EcaFile file) {
		this(symbols, usedEvents(symbols, file), false);
	}

	private static List<EventDeclaration> usedEvents(final EcaBoogieSymbolTable symbols, final EcaFile file) {
		symbols.registerUsedDeclarations(Objects.requireNonNull(file));
		return symbols.occurrenceEventDeclarations();
	}

	/**
	 * Reuses registered event variables and registers missing events. Duplicate ECA event declarations are rejected.
	 */
	public EcaBoogieEventEncoding(final EcaBoogieSymbolTable symbols,
			final Collection<? extends EventDeclaration> declarations) {
		this(symbols, declarations, true);
	}

	private EcaBoogieEventEncoding(final EcaBoogieSymbolTable symbols,
			final Collection<? extends EventDeclaration> declarations, final boolean createStatuses) {
		mSymbols = Objects.requireNonNull(symbols);
		final Map<String, EventDeclaration> byName = new LinkedHashMap<>();
		for (final EventDeclaration declaration : List.copyOf(declarations)) {
			final String name = Objects.requireNonNull(declaration.getName());
			if (name.isBlank() || byName.putIfAbsent(name, declaration) != null) {
				throw new IllegalArgumentException("Invalid or duplicate event declaration '" + name + "'");
			}
			if (symbols.lookupGlobal(name).isPresent() && symbols.lookupEventDeclaration(name).isEmpty()) {
				throw new IllegalArgumentException("Event '" + name + "' conflicts with an ordinary variable");
			}
			if (symbols.lookupEventDeclaration(name).isPresent()
					&& (symbols.lookupEventDeclaration(name).orElseThrow().getClass() != declaration.getClass())) {
				throw new IllegalArgumentException("Event kind does not match registered event '" + name + "'");
			}
		}
		for (final EventDeclaration declaration : byName.values()) {
			if (createStatuses && declaration instanceof final InternalEventDeclaration internal) {
				symbols.getOrCreateActionStatus(internal);
			}
			final VariableInfo variable = symbols.getOrCreateEvent(declaration);
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

	/** Initializes all event-occurrence flags to false. This is intended to be called once at program startup. */
	public void addInitialization(final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		final List<Statement> statements = new ArrayList<>();
		for (final EventDescriptor event : mEvents.values()) {
			statements.add(assignment(event, false, target.getLocation()));
		}
		target.addStatements(statements);
	}

	/**
	 * Samples each external Boolean flag nondeterministically, allowing both true and false at every time step. No
	 * integer 0/1 constraint is necessary for a Boolean variable. Internal flags are unaffected by this method.
	 */
	public void addExternalEventHandling(final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		target.addStatements(externalEventStatements(target.getLocation()));
	}

	/** Statements for one main-loop iteration: sample external events, then reset internal occurrences. */
	public List<Statement> timeStepStatements(final ILocation location) {
		final List<Statement> statements = new ArrayList<>(externalEventStatements(location));
		for (final EventDescriptor event : mEvents.values()) {
			if (!event.isExternal()) {
				statements.add(assignment(event, false, EcaBoogieSymbolTable.sourceOrDefault(location)));
			}
		}
		return List.copyOf(statements);
	}

	private List<Statement> externalEventStatements(final ILocation location) {
		return mEvents.values().stream().filter(EventDescriptor::isExternal)
				.<Statement> map(event -> mSymbols.havoc(event.variable(), location)).toList();
	}

	/** Records an internal action event. External occurrences are supplied by addExternalEventHandling instead. */
	public void addEventOccurrence(final String eventName, final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		target.addStatement(occurrenceStatement(eventName, target.getLocation()));
	}

	/** Builds an occurrence update for insertion into a larger atomic action block. */
	public Statement occurrenceStatement(final String eventName, final ILocation location) {
		final EventDescriptor event = requireEvent(eventName);
		if (event.isExternal()) {
			throw new IllegalArgumentException("Action '" + eventName + "' must refer to an internal event");
		}
		return assignment(event, true, EcaBoogieSymbolTable.sourceOrDefault(location));
	}

	private Expression namedCondition(final String name, final boolean external, final ILocation location) {
		final EventDescriptor event = requireEvent(name);
		if (event.isExternal() != external) {
			throw new IllegalArgumentException(
					"Event '" + name + "' must be declared " + (external ? "extern" : "intern"));
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
