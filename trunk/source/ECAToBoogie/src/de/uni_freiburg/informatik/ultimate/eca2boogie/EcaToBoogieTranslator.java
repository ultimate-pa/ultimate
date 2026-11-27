package de.uni_freiburg.informatik.ultimate.eca2boogie;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.typechecker.VariableInfo;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.EcaFile;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.IntegerDeclaration;
import de.uni_freiburg.informatik.ultimate.eca.parser.ast.generated.VariableDeclaration;

/**
 * Constructs runtime, rule, and action code for a checked ECA AST, registering only syntactically used variables. Time
 * is measured in integer milliseconds; months and years use fixed approximations in EcaBoogieTimeEncoding.
 */
public final class EcaToBoogieTranslator {
	private static final String CLOCK_PROCEDURE = "eca$updateTime";
	private final EcaFile mFile;
	private final EcaBoogieSymbolTable mSymbols = new EcaBoogieSymbolTable();
	private final ILocation mLocation;
	private final Unit mUnit;

	public EcaToBoogieTranslator(final EcaFile file) {
		mFile = Objects.requireNonNull(file);
		mLocation = EcaBoogieSymbolTable.sourceOrDefault(file.getLocation());
		mUnit = translateRuntime();
	}

	public Unit getUnit() {
		return mUnit;
	}

	private Unit translateRuntime() {
		final EcaBoogieEventEncoding events = new EcaBoogieEventEncoding(mSymbols, mFile);
		final String timeId = hasSourceName("time") ? "eca$time" : "time";
		final String mainId = hasSourceName("main") ? "eca$main" : "main";
		final VariableInfo time = mSymbols.registerGlobal(timeId, BoogieType.TYPE_INT, mLocation);
		for (final String id : List.of(CLOCK_PROCEDURE, mainId, BoogieUtils.INIT_PROCEDURE,
				BoogieUtils.START_PROCEDURE)) {
			mSymbols.registerProcedureId(id);
		}
		buildClock(time);
		buildInitialization(time, events);
		buildMain(mainId, events);
		final List<Statement> ruleForks =
				new EcaBoogieRuleTranslator(mSymbols, events, time).translateAndFork(mFile.getRules());
		final EcaBoogieProcedureBuilder start = builder(BoogieUtils.START_PROCEDURE);
		start.addStatement(call(BoogieUtils.INIT_PROCEDURE));
		start.addStatements(ruleForks);
		start.addStatement(call(mainId));
		start.build();
		final List<Declaration> declarations = new ArrayList<>(mSymbols.declarations());
		declarations.addAll(mSymbols.getProcedures());
		return new Unit(mLocation, declarations.toArray(Declaration[]::new));
	}

	private void buildClock(final VariableInfo time) {
		final EcaBoogieProcedureBuilder clock = builder(CLOCK_PROCEDURE);
		final VariableInfo increment = clock.declareLocal("t_new", BoogieType.TYPE_INT, mLocation);
		clock.addStatement(assign(increment, integer("0")));
		clock.addStatement(StatementFactory.constructAtomicStatement(mLocation,
				List.of(mSymbols.havoc(increment, mLocation),
						new AssumeStatement(mLocation,
								binary(Operator.COMPGT, mSymbols.identifier(increment, mLocation), integer("0"))),
						assign(time, binary(Operator.ARITHPLUS, mSymbols.identifier(time, mLocation),
								mSymbols.identifier(increment, mLocation))))));
		clock.build();
	}

	private void buildInitialization(final VariableInfo time, final EcaBoogieEventEncoding events) {
		final EcaBoogieProcedureBuilder init = builder(BoogieUtils.INIT_PROCEDURE);
		init.addStatement(assign(time, integer("0")));
		init.addStatements(sourceVariableUpdates());
		events.addInitialization(init);
		new EcaBoogieStatusEncoding(mSymbols).addInitialization(init);
		for (final VariableInfo timestamp : mSymbols.getActionTimestamps()) {
			init.addStatement(assign(timestamp, integer("0")));
		}
		init.build();
	}

	private List<Statement> sourceVariableUpdates() {
		final List<Statement> updates = new ArrayList<>();
		for (final var declaration : mFile.getDeclarations()) {
			if (declaration instanceof final VariableDeclaration variable) {
				final VariableInfo info = mSymbols.lookupGlobal(variable.getName()).orElse(null);
				if (info == null) {
					continue;
				}
				updates.add(mSymbols.havoc(info, mLocation));
				if (variable instanceof final IntegerDeclaration integer && integer.getAllowedValues() != null) {
					final Expression lower =
							binary(Operator.COMPLEQ, integer(integer.getAllowedValues().getLower().toString()),
									mSymbols.identifier(info, mLocation));
					final Expression upper = binary(Operator.COMPLEQ, mSymbols.identifier(info, mLocation),
							integer(integer.getAllowedValues().getUpper().toString()));
					updates.add(new AssumeStatement(mLocation, binary(Operator.LOGICAND, lower, upper)));
				}
			}
		}
		return updates;
	}

	private void buildMain(final String mainId, final EcaBoogieEventEncoding events) {
		final EcaBoogieProcedureBuilder main = builder(mainId);
		final List<Statement> step = new ArrayList<>();
		step.add(call(CLOCK_PROCEDURE));
		final List<Statement> updates = sourceVariableUpdates();
		updates.addAll(events.timeStepStatements(mLocation));
		if (!updates.isEmpty()) {
			step.add(StatementFactory.constructAtomicStatement(mLocation, updates));
		}
		main.addStatement(new WhileStatement(mLocation, ExpressionFactory.createBooleanLiteral(mLocation, true),
				new LoopInvariantSpecification[0], step.toArray(Statement[]::new)));
		main.build();
	}

	private boolean hasSourceName(final String name) {
		return mFile.getDeclarations().stream().anyMatch(declaration -> name.equals(declaration.getName()));
	}

	private EcaBoogieProcedureBuilder builder(final String id) {
		return new EcaBoogieProcedureBuilder(id, mSymbols, mLocation);
	}

	private Statement call(final String id) {
		return StatementFactory.constructCallStatement(mLocation, false, new VariableLHS[0], id, new Expression[0]);
	}

	private Statement assign(final VariableInfo variable, final Expression value) {
		return StatementFactory.constructSingleAssignmentStatement(mLocation, mSymbols.lhs(variable, mLocation), value);
	}

	private Expression integer(final String value) {
		return ExpressionFactory.createIntegerLiteral(mLocation, value);
	}

	private Expression binary(final Operator operator, final Expression left, final Expression right) {
		return ExpressionFactory.newBinaryExpression(mLocation, operator, left, right);
	}
}
