package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Builds one parameterless main or rule procedure. Its identifier must first be reserved in the symbol table. Locals
 * are obtained from that table, while a Boogie visitor collects writes and calls, including nested statements. As in
 * the C translator's ProcedureManager, modifies clauses include callee effects. No ECA translation rules are encoded
 * here. A successful build registers the resulting Procedure and closes the builder.
 */
public final class EcaBoogieProcedureBuilder {
	private final String mProcedureId;
	private final EcaBoogieSymbolTable mSymbols;
	private final ILocation mLocation;
	private final List<Statement> mStatements = new ArrayList<>();
	private final List<Specification> mSpecifications = new ArrayList<>();
	private final Map<String, VariableInfo> mModifiedGlobals = new LinkedHashMap<>();
	private final Set<String> mCallees = new LinkedHashSet<>();
	private boolean mBuilt;

	public EcaBoogieProcedureBuilder(final String procedureId, final EcaBoogieSymbolTable symbols,
			final ILocation location) {
		mProcedureId = Objects.requireNonNull(procedureId);
		if (procedureId.isBlank()) {
			throw new IllegalArgumentException("A procedure identifier must not be blank");
		}
		mSymbols = Objects.requireNonNull(symbols);
		mLocation = EcaBoogieSymbolTable.sourceOrDefault(location);
		if (symbols.lookupProcedure(procedureId).isPresent()) {
			throw new IllegalArgumentException("Procedure '" + procedureId + "' is already built");
		}
	}

	public String getProcedureId() {
		return mProcedureId;
	}

	public ILocation getLocation() {
		return mLocation;
	}

	EcaBoogieSymbolTable getSymbolTable() {
		return mSymbols;
	}

	public VariableInfo declareLocal(final String id, final BoogieType type, final ILocation location) {
		ensureOpen();
		return mSymbols.registerLocal(mProcedureId, id, type, location);
	}

	public VariableInfo createAuxiliary(final String hint, final BoogieType type, final ILocation location) {
		ensureOpen();
		return mSymbols.createAuxiliary(hint, type, new DeclarationInformation(StorageClass.LOCAL, mProcedureId),
				location);
	}

	public void addStatement(final Statement statement) {
		addStatements(List.of(statement));
	}

	/** Validates the whole collection before adding any statements or effects. Existing expression ASTs are retained. */
	public void addStatements(final Collection<? extends Statement> statements) {
		ensureOpen();
		final List<Statement> copy = List.copyOf(statements);
		final EffectCollector effects = new EffectCollector();
		effects.scan(copy);
		mStatements.addAll(copy);
		mergeEffects(effects);
	}

	/** Requires/ensures clauses are retained; non-free modifies clauses are merged into the generated frame. */
	public void addSpecification(final Specification specification) {
		ensureOpen();
		Objects.requireNonNull(specification);
		if (specification instanceof final ModifiesSpecification modifies) {
			if (modifies.isFree()) {
				throw new IllegalArgumentException("Only non-free modifies clauses are supported");
			}
			final List<VariableInfo> variables = resolveModifiedGlobals(modifies, mSymbols);
			for (final VariableInfo variable : variables) {
				mModifiedGlobals.put(variable.getName(), variable);
			}
		} else if (specification instanceof RequiresSpecification || specification instanceof EnsuresSpecification) {
			mSpecifications.add(specification);
		} else {
			throw new IllegalArgumentException("A procedure requires a requires, ensures, or modifies specification");
		}
	}

	public void recordModifiedGlobal(final VariableInfo variable) {
		ensureOpen();
		validateGlobal(variable);
		mModifiedGlobals.put(variable.getName(), variable);
	}

	/** Records an additional dependency, for example a call that will be inserted by a later construction step. */
	public void recordCall(final String callee) {
		ensureOpen();
		if (Objects.requireNonNull(callee).isBlank()) {
			throw new IllegalArgumentException("A callee identifier must not be blank");
		}
		mCallees.add(callee);
	}

	public Set<VariableInfo> getModifiedGlobals() {
		refreshEffects();
		return Collections.unmodifiableSet(new LinkedHashSet<>(mModifiedGlobals.values()));
	}

	public Set<String> getCallees() {
		refreshEffects();
		return Collections.unmodifiableSet(new LinkedHashSet<>(mCallees));
	}

	/** Builds using completed callees (and self-recursion). For mutually dependent builders compute the closure first. */
	public Procedure build() {
		ensureOpen();
		return build(computeEffectiveModifiedGlobals(List.of(this)).get(mProcedureId));
	}

	/**
	 * Builds and registers a combined declaration/body. Pass the closure for this procedure from
	 * computeEffectiveModifiedGlobals when callees are still being built. Additional globals conservatively enlarge the
	 * frame; directly recorded writes are always included.
	 */
	public Procedure build(final Collection<VariableInfo> effectiveModifiedGlobals) {
		ensureOpen();
		refreshEffects();
		final Map<String, VariableInfo> modified = new LinkedHashMap<>(mModifiedGlobals);
		for (final VariableInfo variable : Objects.requireNonNull(effectiveModifiedGlobals)) {
			validateGlobal(variable);
			modified.put(variable.getName(), variable);
		}
		final List<Specification> specifications = new ArrayList<>(mSpecifications);
		if (!modified.isEmpty()) {
			final VariableLHS[] lhs = modified.values().stream().map(v -> mSymbols.lhs(v, mLocation))
					.toArray(VariableLHS[]::new);
			specifications.add(new ModifiesSpecification(mLocation, false, lhs));
		}
		final Body body = new Body(mLocation, mSymbols.localDeclarations(mProcedureId).toArray(VariableDeclaration[]::new),
				mStatements.toArray(Statement[]::new));
		final Procedure result = new Procedure(mLocation, new Attribute[0], mProcedureId, new String[0], new VarList[0],
				new VarList[0], specifications.toArray(Specification[]::new), body);
		mSymbols.registerProcedure(result);
		mBuilt = true;
		return result;
	}

	/** Computes a fixed point of global writes over the call graph, including recursive calls. */
	public static Map<String, Set<VariableInfo>> computeEffectiveModifiedGlobals(
			final Collection<EcaBoogieProcedureBuilder> builders) {
		final Map<String, EcaBoogieProcedureBuilder> byId = new LinkedHashMap<>();
		final Map<String, Set<VariableInfo>> result = new LinkedHashMap<>();
		EcaBoogieSymbolTable symbols = null;
		for (final EcaBoogieProcedureBuilder builder : List.copyOf(builders)) {
			if (symbols != null && symbols != builder.mSymbols) {
				throw new IllegalArgumentException("Procedure builders must share one symbol table");
			}
			symbols = builder.mSymbols;
			if (byId.putIfAbsent(builder.mProcedureId, builder) != null) {
				throw new IllegalArgumentException("Duplicate procedure builder for '" + builder.mProcedureId + "'");
			}
			result.put(builder.mProcedureId, new LinkedHashSet<>(builder.getModifiedGlobals()));
		}
		boolean changed;
		do {
			changed = false;
			for (final EcaBoogieProcedureBuilder builder : byId.values()) {
				for (final String callee : builder.getCallees()) {
					Set<VariableInfo> effects = result.get(callee);
					if (effects == null) {
						final Procedure procedure = builder.mSymbols.lookupProcedure(callee).orElseThrow(
								() -> new IllegalArgumentException("No builder or completed procedure for callee '" + callee + "'"));
						if (procedure.getSpecification() == null) {
							throw new IllegalArgumentException("Callee '" + callee + "' has no procedure specification");
						}
						effects = new LinkedHashSet<>();
						for (final Specification specification : procedure.getSpecification()) {
							if (specification instanceof final ModifiesSpecification modifies) {
								effects.addAll(resolveModifiedGlobals(modifies, builder.mSymbols));
							}
						}
					}
					changed |= result.get(builder.mProcedureId).addAll(effects);
				}
			}
		} while (changed);
		result.replaceAll((id, effects) -> Collections.unmodifiableSet(new LinkedHashSet<>(effects)));
		return Collections.unmodifiableMap(result);
	}

	private static List<VariableInfo> resolveModifiedGlobals(final ModifiesSpecification specification,
			final EcaBoogieSymbolTable symbols) {
		final List<VariableInfo> result = new ArrayList<>();
		for (final VariableLHS lhs : specification.getIdentifiers()) {
			if (lhs.getDeclarationInformation() != null
					&& lhs.getDeclarationInformation().getStorageClass() != StorageClass.GLOBAL) {
				throw new IllegalArgumentException("A modifies clause may only name global variables");
			}
			result.add(symbols.lookupGlobal(lhs.getIdentifier()).orElseThrow(
					() -> new IllegalArgumentException("Unknown modified global '" + lhs.getIdentifier() + "'")));
		}
		return result;
	}

	private void validateGlobal(final VariableInfo variable) {
		Objects.requireNonNull(variable);
		if (mSymbols.lookupGlobal(variable.getName()).orElse(null) != variable) {
			throw new IllegalArgumentException("Variable '" + variable.getName() + "' is not a global in this symbol table");
		}
	}

	private void refreshEffects() {
		final EffectCollector effects = new EffectCollector();
		effects.scan(mStatements);
		mergeEffects(effects);
	}

	private void mergeEffects(final EffectCollector effects) {
		mModifiedGlobals.putAll(effects.mGlobals);
		mCallees.addAll(effects.mCalls);
	}

	private void ensureOpen() {
		if (mBuilt) {
			throw new IllegalStateException("Procedure '" + mProcedureId + "' is already built");
		}
	}

	private final class EffectCollector extends BoogieVisitor {
		private final Map<String, VariableInfo> mGlobals = new LinkedHashMap<>();
		private final Set<String> mCalls = new LinkedHashSet<>();

		void scan(final Collection<? extends Statement> statements) {
			for (final Statement statement : statements) {
				processStatement(statement);
			}
		}

		@Override
		protected void visit(final VariableLHS lhs) {
			final VariableInfo variable = mSymbols.lookupVariable(mProcedureId, lhs.getIdentifier()).orElseThrow(
					() -> new IllegalArgumentException("Unknown assignment target '" + lhs.getIdentifier() + "'"));
			if (lhs.getDeclarationInformation() != null
					&& !lhs.getDeclarationInformation().equals(variable.getDeclarationInformation())) {
				throw new IllegalArgumentException("Assignment target '" + lhs.getIdentifier() + "' has conflicting scope");
			}
			if (lhs.getType() != null && !lhs.getType().equals(variable.getType())) {
				throw new IllegalArgumentException("Assignment target '" + lhs.getIdentifier() + "' has conflicting type");
			}
			if (variable.getDeclarationInformation().getStorageClass() == StorageClass.GLOBAL) {
				mGlobals.put(variable.getName(), variable);
			}
		}

		@Override
		protected void visit(final CallStatement statement) {
			mCalls.add(statement.getMethodName());
		}

		@Override
		protected void visit(final ForkStatement statement) {
			mCalls.add(statement.getProcedureName());
		}
	}
}
