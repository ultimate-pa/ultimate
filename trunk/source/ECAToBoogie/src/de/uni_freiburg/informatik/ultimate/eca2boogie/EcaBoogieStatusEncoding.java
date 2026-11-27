package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.EcaStatus;

/**
 * Exact four-valued status encoding, independent of event-occurrence flags. Status is global per internal action name.
 * The caller chooses when lifecycle transitions happen; setting a status does not emit an event, or vice versa.
 */
public final class EcaBoogieStatusEncoding {
	private final EcaBoogieSymbolTable mSymbols;

	public EcaBoogieStatusEncoding(final EcaBoogieSymbolTable symbols) {
		mSymbols = Objects.requireNonNull(symbols);
	}

	public static IdentifierExpression literal(final EcaStatus status, final ILocation location) {
		return ExpressionFactory.constructIdentifierExpression(EcaBoogieSymbolTable.sourceOrDefault(location),
				EcaStatus.TYPE, Objects.requireNonNull(status).name(), DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	/** Include once per Unit. Unique constants plus exhaustiveness make this an enum, not an unconstrained sort. */
	public static List<Declaration> declarations() {
		final ILocation location = EcaBoogieSymbolTable.createDefaultLocation();
		final String[] names = java.util.Arrays.stream(EcaStatus.values()).map(Enum::name).toArray(String[]::new);
		final TypeDeclaration type = new TypeDeclaration(location, new Attribute[0], true, "status", new String[0]);
		final ConstDeclaration constants = new ConstDeclaration(location, new Attribute[0], true,
				new VarList(location, names, EcaStatus.TYPE.toASTType(location)), null, false);
		final String boundName = "eca$status$value";
		final Expression bound = ExpressionFactory.constructIdentifierExpression(location, EcaStatus.TYPE, boundName,
				new DeclarationInformation(StorageClass.QUANTIFIED, null));
		Expression alternatives = null;
		for (final EcaStatus status : EcaStatus.values()) {
			final Expression equality =
					ExpressionFactory.newBinaryExpression(location, Operator.COMPEQ, bound, literal(status, location));
			alternatives = alternatives == null ? equality
					: ExpressionFactory.newBinaryExpression(location, Operator.LOGICOR, alternatives, equality);
		}
		final Axiom exhaustive = new Axiom(location, new Attribute[0],
				ExpressionFactory.quantifier(location, true,
						List.of(new VarList(location, new String[] { boundName }, EcaStatus.TYPE.toASTType(location))),
						alternatives));
		return List.of(type, constants, exhaustive);
	}

	/** Explicit startup initialization; ordinary variables and occurrence flags are untouched. */
	public void addInitialization(final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		final List<Statement> statements = new ArrayList<>();
		for (final var variable : mSymbols.getActionStatusVariables()) {
			statements.add(StatementFactory.constructSingleAssignmentStatement(target.getLocation(),
					mSymbols.lhs(variable, target.getLocation()), literal(EcaStatus.PENDING, target.getLocation())));
		}
		target.addStatements(statements);
	}

	/** Explicit lifecycle update shared by all rules executing this action name. */
	public void addStatusUpdate(final String actionName, final EcaStatus status,
			final EcaBoogieProcedureBuilder target) {
		checkTarget(target);
		final var variable = mSymbols.lookupActionStatusVariable(actionName)
				.orElseThrow(() -> new IllegalArgumentException("Unknown internal action '" + actionName + "'"));
		target.addStatement(StatementFactory.constructSingleAssignmentStatement(target.getLocation(),
				mSymbols.lhs(variable, target.getLocation()), literal(status, target.getLocation())));
	}

	private void checkTarget(final EcaBoogieProcedureBuilder target) {
		if (Objects.requireNonNull(target).getSymbolTable() != mSymbols) {
			throw new IllegalArgumentException("Status encoding and procedure builder must share one symbol table");
		}
	}
}
