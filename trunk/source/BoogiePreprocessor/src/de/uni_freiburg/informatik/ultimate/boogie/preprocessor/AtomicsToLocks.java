package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer.MemorySliceUtils;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

public class AtomicsToLocks extends BoogieTransformer implements IUnmanagedObserver {
	private static final String ULTIMATE_START = "ULTIMATE.start";

	private final BoogiePreprocessorBacktranslator mTranslator;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final DummyVarDeclarationBuilder mDeclarationBuilder;
	private Statement mInitStatement;

	protected AtomicsToLocks(final BoogiePreprocessorBacktranslator translator,
			final IUltimateServiceProvider services) {
		mTranslator = translator;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mDeclarationBuilder = constructDeclarationBuilder();
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter. This function descends
	 * to the unit node and then searches for all atomic blocks and replaces them with lock-based code
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			final VariableDeclaration declaration = mDeclarationBuilder.getDeclaration();
			initializeLockInUnit(unit);
			final List<Declaration> newDeclarations = new ArrayList<>();
			newDeclarations.add(declaration);
			for (final Declaration decl : unit.getDeclarations()) {
				if (decl instanceof Procedure) {
					Procedure proc = (Procedure) decl;
					if (proc.getBody() != null) {
						replaceAtomics(proc);
						proc = addLockToSpecification(proc, mDeclarationBuilder.getLhs());
					}
					newDeclarations.add(proc);
				} else {
					newDeclarations.add(decl);
				}
			}
			unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
			return false;
		}
		return true;
	}

	private DummyVarDeclarationBuilder constructDeclarationBuilder() {
		final String typeName = "bool";
		final NamedType astType = new NamedType(null, BoogieType.TYPE_BOOL, typeName, new ASTType[0]);
		return new DummyVarDeclarationBuilder(astType);
	}

	private void initializeLockInUnit(final Unit unit) {
		final var numDec = unit.getDeclarations().length;
		final var declarations = Arrays.copyOf(unit.getDeclarations(), numDec);
		for (int i = 0; i < numDec; i++) {
			final Declaration decl = declarations[i];
			if (decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals(ULTIMATE_START)) {
				final var startProc = (Procedure) decl;
				final var body = startProc.getBody();
				final var block = body.getBlock();
				final var newBlock = addInitStatement(block);
				body.setBlock(newBlock);
			}
		}
	}

	private Statement[] addInitStatement(final Statement[] blockStatements) {
		final int numStmt = blockStatements.length;
		final Statement[] newStatements = new Statement[numStmt + 1];
		mInitStatement = getLockAssignment(false);
		newStatements[0] = blockStatements[0];
		newStatements[1] = mInitStatement;
		for (int i = 1; i < numStmt; i++) {
			newStatements[i + 1] = blockStatements[i];
		}
		return newStatements;
	}

	private Procedure addLockToSpecification(final Procedure proc, final VariableLHS lhs) {
		final var spec = proc.getSpecification();
		final var modifiesLockSpec = new ModifiesSpecification(DummyVarDeclarationBuilder.getDummyLocation(), false,
				new VariableLHS[] { lhs });
		final var newSpecification = Arrays.copyOf(spec, spec.length + 1);
		newSpecification[spec.length] = modifiesLockSpec;
		return new Procedure(proc.getLoc(), proc.getAttributes(), proc.getIdentifier(), proc.getTypeParams(),
				proc.getInParams(), proc.getOutParams(), newSpecification, proc.getBody());
	}

	private void replaceAtomics(final Procedure proc) {
		final Body body = proc.getBody();

		final var newStatements = processStatements(body.getBlock());

		body.setBlock(newStatements);
	}

	@Override
	protected Statement[] processStatements(final Statement[] statements) {
		final var assume = getAssumeStatement();
		final List<Statement> statementList = new ArrayList<>();
		for (final Statement statement : statements) {
			if (statement instanceof final AtomicStatement atomicstmt) {
				final var lockedSection = processAtomic(atomicstmt);
				statementList.addAll(lockedSection);
				continue;
			}
			if (!(statement instanceof final Label) && (statement != mInitStatement)) {
				statementList.add(assume);
			}
			statementList.add(processStatement(statement));
		}
		return statementList.toArray(new Statement[statementList.size()]);
	}

	private AssumeStatement getAssumeStatement() {
		final var falseLiteral =
				new BooleanLiteral(DummyVarDeclarationBuilder.getDummyLocation(), BoogieType.TYPE_BOOL, false);
		final var negatedLock = ExpressionFactory.constructUnaryExpression(
				DummyVarDeclarationBuilder.getDummyLocation(), Operator.LOGICNEG,
				new IdentifierExpression(DummyVarDeclarationBuilder.getDummyLocation(), BoogieType.TYPE_BOOL,
						mDeclarationBuilder.getIdentifier(), DeclarationInformation.DECLARATIONINFO_GLOBAL));
		return new AssumeStatement(DummyVarDeclarationBuilder.getDummyLocation(), negatedLock);
	}

	private Statement getLockAssignment(final boolean val) {
		final Expression assignment = ExpressionFactory.createBooleanLiteral(null, val);
		final LeftHandSide[] lhs = { mDeclarationBuilder.getLhs() };
		return StatementFactory.constructAssignmentStatement(DummyVarDeclarationBuilder.getDummyLocation(), lhs,
				new Expression[] { assignment });
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		Statement newStatement = null;
		if (statement instanceof final AssertStatement assertStmt) {
			newStatement = statement;
		} else if (statement instanceof final AssignmentStatement assign) {
			newStatement = statement;
		} else if (statement instanceof final AssumeStatement assumeStmt) {
			newStatement = statement;
		} else if (statement instanceof final HavocStatement havoc) {
			newStatement = statement;
		} else if (statement instanceof final CallStatement call) {
			newStatement = statement;
		} else if (statement instanceof final IfStatement ifstmt) {
			final Expression cond = ifstmt.getCondition();
			final Statement[] thens = ifstmt.getThenPart();
			final Statement[] newThens = processStatements(thens);
			final Statement[] elses = ifstmt.getElsePart();
			final Statement[] newElses = processStatements(elses);
			if (newThens != thens || newElses != elses) {
				newStatement = new IfStatement(ifstmt.getLocation(), cond, newThens, newElses);
			}
		} else if (statement instanceof final WhileStatement whilestmt) {
			final Expression cond = whilestmt.getCondition();
			final LoopInvariantSpecification[] invs = whilestmt.getInvariants();
			final LoopInvariantSpecification[] newInvs = processLoopSpecifications(invs);
			final Statement[] body = whilestmt.getBody();
			final Statement[] newBody = processStatements(body);
			if (newInvs != invs || newBody != body) {
				newStatement = new WhileStatement(whilestmt.getLocation(), cond, newInvs, newBody);
			}
		} else {
			/* No recursion for label, havoc, break, return and goto */
			return statement;
		}
		ModelUtils.copyAnnotations(statement, newStatement);
		return newStatement;
	}

	private List<Statement> processAtomic(final AtomicStatement atomicStatement) {
		final List<Statement> lockedStatements = new ArrayList<>();
		final var compareLock = getAssumeStatement();
		final var setLock = getLockAssignment(true);
		final var compareAndSet = new AtomicStatement(DummyVarDeclarationBuilder.getDummyLocation(),
				new Statement[] { compareLock, setLock });
		lockedStatements.add(compareAndSet);
		final var noNestedAtomics = removeAtomics(atomicStatement.getBody());
		lockedStatements.addAll(noNestedAtomics);
		lockedStatements.add(getLockAssignment(false));
		return lockedStatements;
	}

	private List<Statement> removeAtomics(final Statement[] statements) {
		final List<Statement> statementList = new ArrayList<>();
		for (final Statement statement : statements) {
			statementList.addAll(removeAtomics(statement));
		}
		return statementList;
	}

	private List<Statement> removeAtomics(final Statement statement) {
		Statement newStatement = null;
		if (statement instanceof final IfStatement ifstmt) {
			final Expression cond = ifstmt.getCondition();
			final Statement[] thens = ifstmt.getThenPart();
			final Statement[] newThens = removeAtomics(thens).toArray(new Statement[0]);
			final Statement[] elses = ifstmt.getElsePart();
			final Statement[] newElses = removeAtomics(elses).toArray(new Statement[0]);
			if (newThens != thens || newElses != elses) {
				newStatement = new IfStatement(ifstmt.getLocation(), cond, newThens, newElses);
			}
		} else if (statement instanceof final WhileStatement whilestmt) {
			final Expression cond = whilestmt.getCondition();
			final LoopInvariantSpecification[] invs = whilestmt.getInvariants();
			final LoopInvariantSpecification[] newInvs = processLoopSpecifications(invs);
			final Statement[] body = whilestmt.getBody();
			final Statement[] newBody = removeAtomics(body).toArray(new Statement[0]);
			if (newInvs != invs || newBody != body) {
				newStatement = new WhileStatement(whilestmt.getLocation(), cond, newInvs, newBody);
			}
		} else if (statement instanceof final AtomicStatement atomicStatement) {
			return removeAtomics(atomicStatement.getBody());
		} else {
			return List.of(statement);
		}
		ModelUtils.copyAnnotations(statement, newStatement);
		return List.of(newStatement);
	}

	private boolean atomicContainsLoop(final AtomicStatement atomicBlock) {
		final var body = atomicBlock.getBody();
		for (final Statement statement : body) {
			if (containsLoop(statement)) {
				return true;
			}
		}
		return false;
	}

	private boolean containsLoop(final Statement statement) {
		return false;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {

	}

	@Override
	public void finish() {

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	private static final class DummyVarDeclarationBuilder {
		// TODO Construct unique identifier
		private static final String IDENTIFIER = "lock";
		private static int SUFFIX = 0;

		private static BoogieType BOOL = BoogieType.TYPE_BOOL;
		private final String mIdentifier;

		private final VariableDeclaration mVariableDeclaration;
		private final ASTType mAstType;
		private final VariableLHS mLhs;

		public DummyVarDeclarationBuilder(final ASTType astType) {
			mAstType = astType;
			mIdentifier = constructIdentifier();
			mVariableDeclaration = constructDeclaration();
			mLhs = setLhs(mVariableDeclaration.getLoc());
		}

		private VariableDeclaration constructDeclaration() {
			final var loc = getDummyLocation();
			return new VariableDeclaration(loc, new Attribute[0],
					new VarList[] { new VarList(loc, new String[] { mIdentifier }, mAstType) });
		}

		private String constructIdentifier() {
			return IDENTIFIER + MemorySliceUtils.constructMemorySliceSuffix(SUFFIX);
		}

		public static ILocation getDummyLocation() {
			return new DefaultLocation();
		}

		private VariableLHS setLhs(final ILocation loc) {
			return ExpressionFactory.constructVariableLHS(loc, BOOL, mIdentifier,
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
		}

		public VariableDeclaration getDeclaration() {
			return mVariableDeclaration;
		}

		public VariableLHS getLhs() {
			return mLhs;
		}

		public String getIdentifier() {
			return mIdentifier;
		}
	}
}
