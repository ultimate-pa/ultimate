package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.EcaStatus;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.BooleanDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaRule;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.ExternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.FalseEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.IntegerDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEvent;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.InternalEventDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.TrueExternalEvent;

/**
 * Registers variables and procedures while constructing a Boogie program from an ECA file. Source variables and action
 * statuses retain their identifiers; event-occurrence flags have separate generated names. Procedure scopes are
 * explicit, and rule-to-procedure mappings use AST-node identity.
 */
public final class EcaBoogieSymbolTable {
	private final Map<DeclarationInformation, Map<String, VariableInfo>> mVariables = new LinkedHashMap<>();
	private final Map<String, VariableInfo> mEventVariables = new LinkedHashMap<>();
	private final Map<String, VariableInfo> mActionStatusVariables = new LinkedHashMap<>();
	private final Map<String, VariableInfo> mActionTimestamps = new LinkedHashMap<>();
	private final Map<String, EventDeclaration> mEventDeclarations = new LinkedHashMap<>();
	private final Set<String> mProcedureIds = new LinkedHashSet<>();
	private final Map<EcaRule, String> mRuleProcedureIds = new IdentityHashMap<>();
	private final Map<String, Procedure> mProcedures = new LinkedHashMap<>();
	private final Set<String> mUsedNames = new LinkedHashSet<>();
	private long mAuxiliaryCounter;

	/** Registers a separate occurrence flag and, for internal events, a same-named global action status. */
	public VariableInfo registerEvent(final EventDeclaration declaration) {
		Objects.requireNonNull(declaration);
		final String name = declaration.getName();
		checkName(name);
		if (mEventVariables.containsKey(name) || lookupGlobal(name).isPresent() || mProcedureIds.contains(name)) {
			throw new IllegalArgumentException("Event '" + name + "' conflicts with an existing declaration");
		}
		rememberEvent(declaration);
		if (declaration instanceof final InternalEventDeclaration internal) {
			getOrCreateActionStatus(internal);
		}
		return constructEventFlag(declaration);
	}

	private VariableInfo constructEventFlag(final EventDeclaration declaration) {
		final String name = declaration.getName();
		// '$' cannot occur in source ECA identifiers, so future source declarations cannot collide with this flag.
		final String id = freshGeneratedId("eca$event$" + name);
		final VariableInfo variable = registerGlobal(id, BoogieType.TYPE_BOOL, declaration.getLocation());
		mEventVariables.put(name, variable);
		mUsedNames.add(name);
		return variable;
	}

	public VariableInfo getOrCreateEvent(final EventDeclaration declaration) {
		rememberEvent(declaration);
		final VariableInfo existing = mEventVariables.get(declaration.getName());
		return existing == null ? constructEventFlag(declaration) : existing;
	}

	public VariableInfo getOrCreateActionStatus(final InternalEventDeclaration declaration) {
		rememberEvent(declaration);
		return mActionStatusVariables.computeIfAbsent(declaration.getName(), name -> registerVariable(name,
				EcaStatus.TYPE, DeclarationInformation.DECLARATIONINFO_GLOBAL, declaration.getLocation(), true));
	}

	/** One global last-occurrence timestamp per executed action name, shared across parallel rules. */
	public VariableInfo getOrCreateActionTimestamp(final InternalEventDeclaration declaration) {
		rememberEvent(declaration);
		return mActionTimestamps.computeIfAbsent(declaration.getName(),
				name -> registerGlobal(freshGeneratedId("eca$actionTime$" + name), BoogieType.TYPE_INT,
						declaration.getLocation()));
	}

	public Optional<VariableInfo> lookupActionTimestamp(final String actionName) {
		return Optional.ofNullable(mActionTimestamps.get(actionName));
	}

	public List<VariableInfo> getActionTimestamps() {
		return List.copyOf(mActionTimestamps.values());
	}

	public Optional<EventDeclaration> lookupEventDeclaration(final String name) {
		return Optional.ofNullable(mEventDeclarations.get(name));
	}

	public List<EventDeclaration> occurrenceEventDeclarations() {
		return mEventVariables.keySet().stream().map(mEventDeclarations::get).toList();
	}

	private void rememberEvent(final EventDeclaration declaration) {
		Objects.requireNonNull(declaration);
		checkName(declaration.getName());
		if (mProcedureIds.contains(declaration.getName())) {
			throw new IllegalArgumentException("Event conflicts with procedure '" + declaration.getName() + "'");
		}
		final EventDeclaration previous = mEventDeclarations.get(declaration.getName());
		if (previous != null && previous.getClass() != declaration.getClass()) {
			throw new IllegalArgumentException("Conflicting event kind for '" + declaration.getName() + "'");
		}
		if (lookupGlobal(declaration.getName()).isPresent()
				&& !mActionStatusVariables.containsKey(declaration.getName())) {
			throw new IllegalArgumentException("Event conflicts with variable '" + declaration.getName() + "'");
		}
		mEventDeclarations.putIfAbsent(declaration.getName(), declaration);
		mUsedNames.add(declaration.getName());
	}

	private String freshGeneratedId(final String prefix) {
		String id = prefix;
		while (mUsedNames.contains(id)) {
			id = prefix + "$" + mAuxiliaryCounter++;
		}
		return id;
	}

	/** Registers only referenced roles of declarations in an already checked file. Safe to call again. */
	public void registerUsedDeclarations(final EcaFile file) {
		final EcaBoogieUsageAnalysis usage = EcaBoogieUsageAnalysis.analyze(file);
		final Set<String> conditions = usage.conditionNames();
		final Set<String> events = usage.eventNames();
		final Set<String> actions = usage.actionNames();
		final Set<String> declared = new LinkedHashSet<>();
		for (final var declaration : file.getDeclarations()) {
			final String name = declaration.getName();
			// Reserve even unused source names for fresh-name generation, without emitting their declarations.
			mUsedNames.add(name);
			if (!declared.add(name)) {
				throw new IllegalArgumentException("Duplicate ECA declaration '" + name + "'");
			}
			if (conditions.contains(name)) {
				if (declaration instanceof final InternalEventDeclaration internal) {
					getOrCreateActionStatus(internal);
				} else if (declaration instanceof final de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.VariableDeclaration variable) {
					getOrCreateSourceVariable(variable);
				} else {
					throw new IllegalArgumentException("External events cannot occur in conditions: " + name);
				}
			}
			if (actions.contains(name)) {
				if (!(declaration instanceof final InternalEventDeclaration internal)) {
					throw new IllegalArgumentException("Action must name a declared internal event: " + name);
				}
				getOrCreateActionStatus(internal);
				getOrCreateActionTimestamp(internal);
			}
			if (events.contains(name)) {
				if (!(declaration instanceof final EventDeclaration event)) {
					throw new IllegalArgumentException("Event must name an event declaration: " + name);
				}
				getOrCreateEvent(event);
			}
		}
	}

	public VariableInfo getOrCreateSourceVariable(
			final de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.VariableDeclaration declaration) {
		final VariableInfo existing = lookupGlobal(declaration.getName()).orElse(null);
		if (existing == null) {
			return registerSourceVariable(declaration);
		}
		final BoogieType expected =
				declaration instanceof IntegerDeclaration ? BoogieType.TYPE_INT : BoogieType.TYPE_BOOL;
		if (!expected.equals(existing.getType()) || mEventDeclarations.containsKey(declaration.getName())) {
			throw new IllegalArgumentException("Conflicting variable declaration '" + declaration.getName() + "'");
		}
		return existing;
	}

	/** Constructs and registers a global variable with the ECA declaration's original identifier and type. */
	public VariableInfo registerSourceVariable(
			final de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.VariableDeclaration declaration) {
		Objects.requireNonNull(declaration);
		final BoogieType type = switch (declaration) {
		case final IntegerDeclaration ignored -> BoogieType.TYPE_INT;
		case final BooleanDeclaration ignored -> BoogieType.TYPE_BOOL;
		};
		return registerGlobal(declaration.getName(), type, declaration.getLocation());
	}

	/** Registers a local variable in an already registered procedure. Local variables may shadow globals. */
	public VariableInfo registerLocal(final String procedureId, final String id, final BoogieType type,
			final ILocation location) {
		requireProcedure(procedureId);
		return registerVariable(id, type, new DeclarationInformation(StorageClass.LOCAL, procedureId), location);
	}

	/**
	 * Allocates a name distinct from all currently registered variable and procedure identifiers. Register source
	 * declarations before allocating auxiliaries. The scope must be global or local to a registered procedure.
	 */
	public VariableInfo createAuxiliary(final String hint, final BoogieType type, final DeclarationInformation scope,
			final ILocation location) {
		checkName(hint);
		checkType(type);
		checkScope(scope);
		final String prefix = "eca_aux_" + hint.replaceAll("[^A-Za-z0-9_]", "_") + "_";
		String id;
		do {
			id = prefix + mAuxiliaryCounter++;
		} while (mUsedNames.contains(id));
		return registerVariable(id, type, scope, location);
	}

	/** Registers a global variable, rejecting an existing declaration rather than silently replacing it. */
	public VariableInfo registerGlobal(final String id, final BoogieType type, final ILocation location) {
		return registerVariable(id, type, DeclarationInformation.DECLARATIONINFO_GLOBAL, location);
	}

	private VariableInfo registerVariable(final String id, final BoogieType type, final DeclarationInformation scope,
			final ILocation location) {
		return registerVariable(id, type, scope, location, false);
	}

	private VariableInfo registerVariable(final String id, final BoogieType type, final DeclarationInformation scope,
			final ILocation location, final boolean actionStatus) {
		checkName(id);
		checkType(type);
		checkScope(scope);
		final Map<String, VariableInfo> variables = mVariables.get(scope);
		if (variables != null && variables.containsKey(id)) {
			throw new IllegalArgumentException("Variable '" + id + "' is already registered in scope " + scope);
		}
		if (scope.getStorageClass() == StorageClass.GLOBAL && mProcedureIds.contains(id)) {
			throw new IllegalArgumentException("Global variable '" + id + "' conflicts with a registered procedure");
		}
		if (scope.getStorageClass() == StorageClass.GLOBAL && mEventDeclarations.containsKey(id) && !actionStatus) {
			throw new IllegalArgumentException("Global variable '" + id + "' conflicts with a registered event");
		}
		final VariableDeclaration declaration = constructVariableDeclaration(id, type, sourceOrDefault(location));
		final VariableInfo variable = new VariableInfo(false, declaration, id, type, scope);
		mVariables.computeIfAbsent(scope, ignored -> new LinkedHashMap<>()).put(id, variable);
		mUsedNames.add(id);
		return variable;
	}

	private static VariableDeclaration constructVariableDeclaration(final String id, final BoogieType type,
			final ILocation location) {
		final VarList variables = new VarList(location, new String[] { id }, type.toASTType(location));
		return new VariableDeclaration(location, new Attribute[0], new VarList[] { variables });
	}

	/** Reserves a procedure identifier before its body is constructed. */
	public void registerProcedureId(final String procedureId) {
		checkName(procedureId);
		if (mProcedureIds.contains(procedureId)) {
			throw new IllegalArgumentException("Procedure '" + procedureId + "' is already registered");
		}
		if (lookupGlobal(procedureId).isPresent() || mEventDeclarations.containsKey(procedureId)) {
			throw new IllegalArgumentException("Procedure '" + procedureId + "' conflicts with a global variable");
		}
		mProcedureIds.add(procedureId);
		mUsedNames.add(procedureId);
	}

	/** Reserves a distinct procedure identifier and associates it with this particular ECA rule node. */
	public void registerRuleProcedure(final EcaRule rule, final String procedureId) {
		Objects.requireNonNull(rule);
		if (mRuleProcedureIds.containsKey(rule)) {
			throw new IllegalArgumentException("A procedure is already registered for this ECA rule");
		}
		registerProcedureId(procedureId);
		mRuleProcedureIds.put(rule, procedureId);
	}

	/** Stores a completed procedure whose identifier was previously reserved. */
	public void registerProcedure(final Procedure procedure) {
		Objects.requireNonNull(procedure);
		final String id = procedure.getIdentifier();
		requireProcedure(id);
		if (mProcedures.putIfAbsent(id, procedure) != null) {
			throw new IllegalArgumentException("A completed procedure is already registered for '" + id + "'");
		}
	}

	public Optional<VariableInfo> lookupGlobal(final String id) {
		return lookup(DeclarationInformation.DECLARATIONINFO_GLOBAL, id);
	}

	public Optional<VariableInfo> lookupLocal(final String procedureId, final String id) {
		checkName(procedureId);
		return lookup(new DeclarationInformation(StorageClass.LOCAL, procedureId), id);
	}

	/** Resolves a local before a global. A null procedure identifier requests global scope only. */
	public Optional<VariableInfo> lookupVariable(final String procedureId, final String id) {
		if (procedureId != null) {
			final Optional<VariableInfo> local = lookupLocal(procedureId, id);
			if (local.isPresent()) {
				return local;
			}
		}
		return lookupGlobal(id);
	}

	private Optional<VariableInfo> lookup(final DeclarationInformation scope, final String id) {
		checkName(id);
		final Map<String, VariableInfo> variables = mVariables.get(scope);
		return variables == null ? Optional.empty() : Optional.ofNullable(variables.get(id));
	}

	/** Only registered events are returned; ordinary Boolean variables are not event variables. */
	public Optional<VariableInfo> lookupEventVariable(final String eventName) {
		checkName(eventName);
		return Optional.ofNullable(mEventVariables.get(eventName));
	}

	/** Resolves the global status of an internal action name; external events have no status. */
	public Optional<VariableInfo> lookupActionStatusVariable(final String actionName) {
		checkName(actionName);
		return Optional.ofNullable(mActionStatusVariables.get(actionName));
	}

	public List<VariableInfo> getActionStatusVariables() {
		return List.copyOf(mActionStatusVariables.values());
	}

	/** Resolves a named event. Constant true/false events have no corresponding variable. */
	public Optional<VariableInfo> lookupEventVariable(final EcaEvent event) {
		return switch (Objects.requireNonNull(event)) {
		case final InternalEvent internal -> lookupEventVariable(internal.getActionId().getName());
		case final ExternalEvent external -> lookupEventVariable(external.getActionId().getName());
		case final TrueExternalEvent ignored -> Optional.empty();
		case final FalseEvent ignored -> Optional.empty();
		};
	}

	public Optional<String> lookupRuleProcedureId(final EcaRule rule) {
		return Optional.ofNullable(mRuleProcedureIds.get(Objects.requireNonNull(rule)));
	}

	/** Empty until the procedure's completed AST has been registered. */
	public Optional<Procedure> lookupProcedure(final String procedureId) {
		checkName(procedureId);
		return Optional.ofNullable(mProcedures.get(procedureId));
	}

	public IdentifierExpression identifier(final VariableInfo variable, final ILocation useLocation) {
		Objects.requireNonNull(variable);
		return ExpressionFactory.constructIdentifierExpression(sourceOrDefault(useLocation), variable.getType(),
				variable.getName(), variable.getDeclarationInformation());
	}

	public VariableLHS lhs(final VariableInfo variable, final ILocation useLocation) {
		Objects.requireNonNull(variable);
		return ExpressionFactory.constructVariableLHS(sourceOrDefault(useLocation), variable.getType(),
				variable.getName(), variable.getDeclarationInformation());
	}

	/** Boogie's nondeterministic assignment, applicable to Boolean, integer, and status variables. */
	public HavocStatement havoc(final VariableInfo variable, final ILocation useLocation) {
		return new HavocStatement(sourceOrDefault(useLocation), new VariableLHS[] { lhs(variable, useLocation) });
	}

	/** Returns variables only. Use declarations() when assembling a Unit, to include the status type and constants. */
	public List<VariableDeclaration> globalDeclarations() {
		return declarations(DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	/** All global declarations, including the exact four-valued status type and constants. Include once per Unit. */
	public List<de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration> declarations() {
		final List<de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration> result =
				new ArrayList<>(EcaBoogieStatusEncoding.declarations());
		result.addAll(globalDeclarations());
		return List.copyOf(result);
	}

	/** Returns an unmodifiable snapshot of this procedure's local declarations. */
	public List<VariableDeclaration> localDeclarations(final String procedureId) {
		checkName(procedureId);
		return declarations(new DeclarationInformation(StorageClass.LOCAL, procedureId));
	}

	private List<VariableDeclaration> declarations(final DeclarationInformation scope) {
		final Map<String, VariableInfo> variables = mVariables.get(scope);
		if (variables == null) {
			return List.of();
		}
		final List<VariableDeclaration> declarations = new ArrayList<>();
		for (final VariableInfo variable : variables.values()) {
			declarations.add((VariableDeclaration) variable.getDeclaration());
		}
		return List.copyOf(declarations);
	}

	/** Returns completed procedures in identifier reservation order, independently of body construction order. */
	public List<Procedure> getProcedures() {
		final List<Procedure> procedures = new ArrayList<>();
		for (final String id : mProcedureIds) {
			final Procedure procedure = mProcedures.get(id);
			if (procedure != null) {
				procedures.add(procedure);
			}
		}
		return List.copyOf(procedures);
	}

	/** Uses the same unknown-location convention as PEAtoBoogie's Req2BoogieTranslator. */
	public static BoogieLocation createDefaultLocation() {
		return new BoogieLocation("", -1, -1, -1, -1);
	}

	public static ILocation sourceOrDefault(final ILocation sourceLocation) {
		return sourceLocation == null ? createDefaultLocation() : sourceLocation;
	}

	private void checkScope(final DeclarationInformation scope) {
		Objects.requireNonNull(scope);
		switch (scope.getStorageClass()) {
		case GLOBAL -> {
			if (scope.getProcedure() != null) {
				throw new IllegalArgumentException("Global scope must not specify a procedure");
			}
		}
		case LOCAL -> requireProcedure(scope.getProcedure());
		default -> throw new IllegalArgumentException("Only global and local variable scopes are supported");
		}
	}

	private void requireProcedure(final String procedureId) {
		checkName(procedureId);
		if (!mProcedureIds.contains(procedureId)) {
			throw new IllegalArgumentException("Unknown procedure '" + procedureId + "'");
		}
	}

	private static void checkName(final String name) {
		if (Objects.requireNonNull(name).isBlank()) {
			throw new IllegalArgumentException("A symbol identifier must not be blank");
		}
		if (EcaStatus.isLiteral(name)) {
			throw new IllegalArgumentException("Reserved status constant '" + name + "' cannot be declared");
		}
	}

	private static void checkType(final BoogieType type) {
		if (BoogieType.TYPE_ERROR.equals(Objects.requireNonNull(type))) {
			throw new IllegalArgumentException("Cannot declare a variable with an error type");
		}
	}
}
