/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer.MemorySliceUtils;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;

public class AtomicsToLocks extends BoogieTransformer implements IUnmanagedObserver {
	private static final String ULTIMATE_START = "ULTIMATE.start";
	private static final String ULTIMATE_INIT = "ULTIMATE.init";
	private static String ATOMIC_BEGIN = "__VERIFIER_atomic_begin";
	private static String ATOMIC_END = "__VERIFIER_atomic_end";

	private final BoogiePreprocessorBacktranslator mTranslator;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private DummyVarDeclarationBuilder mDeclarationBuilder;
	private Statement mInitStatement;
	private BoogieDeclarations mBoogieDeclarations;
	private boolean mContainsAtomic;
	private final Set<String> mModifiesLock = new HashSet<>();

	protected AtomicsToLocks(final BoogiePreprocessorBacktranslator translator,
			final IUltimateServiceProvider services) {
		mTranslator = translator;
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter. This function descends
	 * to the unit node and then searches for all atomic blocks and replaces them with lock-based code
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			mBoogieDeclarations = new BoogieDeclarations(unit, mLogger);
			mDeclarationBuilder = constructDeclarationBuilder(unit);
			final VariableDeclaration declaration = mDeclarationBuilder.getDeclaration();
			final List<Declaration> newDeclarations = new ArrayList<>();
			newDeclarations.add(declaration);
			for (final Declaration decl : unit.getDeclarations()) {
				if (!(decl instanceof Procedure)) {
					newDeclarations.add(decl);
					continue;
				}
				final var proc = (Procedure) decl;
				final var identifier = (proc).getIdentifier();
				final var impl = mBoogieDeclarations.getProcImplementation().get(identifier);
				if (impl == null) {
					newDeclarations.add(proc);
					continue;
				}
				if (!impl.equals(proc)) {
					newDeclarations.add(proc);
					continue;
				}
				if (proc.getBody() != null) {
					replaceAtomics(proc);
				}
				newDeclarations.add(proc);

			}
			initializeLockInUnit();
			getNewSpecifications(newDeclarations);
			unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
			return false;
		}
		return true;
	}

	private void replaceAtomics(final Procedure proc) {
		final Body body = proc.getBody();

		mContainsAtomic = false;
		final var newStatements = processStatements(body.getBlock());
		if (mContainsAtomic) {
			mModifiesLock.add(proc.getIdentifier());
			mContainsAtomic = false;
		}

		body.setBlock(newStatements);
	}

	@Override
	protected Statement[] processStatements(final Statement[] statements) {
		final var assume = getAssumeStatement();
		final List<Statement> statementList = new ArrayList<>();
		boolean verifierAtomicStarted = false;
		for (final Statement statement : statements) {
			if (statement instanceof final AtomicStatement atomicstmt) {
				assert !verifierAtomicStarted
						: "Nested __VERIFIER_atomic calls are not supported by the translation of atomics "
								+ "into lock-based blocks in the BoogiePreprocessor!";
				final var lockedSection = processAtomic(atomicstmt);
				statementList.addAll(lockedSection);
				mContainsAtomic = true;
				continue;
			}
			if (isAtomicBegin(statement)) {
				assert !verifierAtomicStarted
						: "Nested __VERIFIER_atomic calls are not supported by the translation of atomics "
								+ "into lock-based blocks in the BoogiePreprocessor!";
				verifierAtomicStarted = true;
				mContainsAtomic = true;
			}
			if (isAtomicEnd(statement)) {
				verifierAtomicStarted = false;
			}
			if (!(statement instanceof final Label) && (statement != mInitStatement) && !isAtomic(statement)
					&& !verifierAtomicStarted) {
				statementList.add(assume);
			}
			statementList.add(processStatement(statement));
		}
		return statementList.toArray(new Statement[statementList.size()]);
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
			if (call.getMethodName().equals(ATOMIC_BEGIN)) {
				final var compareLock = getAssumeStatement();
				final var setLock = getLockAssignment(true);
				newStatement = new AtomicStatement(mDeclarationBuilder.getDummyLocation(),
						new Statement[] { compareLock, setLock });
			} else if (call.getMethodName().equals(ATOMIC_END)) {
				newStatement = getLockAssignment(false);
			} else {
				newStatement = statement;
			}
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

	private void getNewSpecifications(final List<Declaration> declarations) {
		for (final String procId : mModifiesLock) {
			final var procSpec = mBoogieDeclarations.getProcSpecification().get(procId);
			assert procSpec != null : "There exists no specification of procedure " + procId;
			final var newSpec = addLockToSpecification(procSpec, mDeclarationBuilder.getLhs());
			final var specIdx = declarations.indexOf(procSpec);
			assert specIdx > -1 : "Declaration of the procedure " + procId + " is missing!";
			declarations.set(specIdx, newSpec);
		}
	}

	private DummyVarDeclarationBuilder constructDeclarationBuilder(final Unit unit) {
		final String typeName = "bool";
		final NamedType astType = new NamedType(null, BoogieType.TYPE_BOOL, typeName, new ASTType[0]);
		return new DummyVarDeclarationBuilder(astType, unit);
	}

	private void initializeLockInUnit() {
		Procedure initProc = null;
		Procedure startProc = null;
		for (final Procedure procedure : mBoogieDeclarations.getProcImplementation().values()) {
			if (procedure.getIdentifier().equals(ULTIMATE_INIT)) {
				initProc = procedure;
				break;
			}
			if (procedure.getIdentifier().equals(ULTIMATE_START)) {
				startProc = procedure;
			}
		}
		assert (initProc != null) || (startProc != null)
				: "The setting replace atomics requires a procedure named " + ULTIMATE_INIT + " or " + ULTIMATE_START;
		if (initProc != null) {
			initializeLockInProc(initProc);
		} else {
			initializeLockInProc(startProc);
		}
	}

	private void initializeLockInProc(final Procedure procedure) {
		final var body = procedure.getBody();
		final var block = body.getBlock();
		final var newBlock = addInitStatement(block);
		body.setBlock(newBlock);
		mModifiesLock.add(procedure.getIdentifier());
	}

	private Statement[] addInitStatement(final Statement[] blockStatements) {
		final int numStmt = blockStatements.length;
		final Statement[] newStatements = new Statement[numStmt + 1];
		mInitStatement = getLockAssignment(false);
		newStatements[0] = mInitStatement;
		for (int i = 0; i < numStmt; i++) {
			newStatements[i + 1] = blockStatements[i];
		}
		return newStatements;
	}

	private Procedure addLockToSpecification(final Procedure proc, final VariableLHS lhs) {
		final var spec = proc.getSpecification();
		final var modifiesLockSpec =
				new ModifiesSpecification(mDeclarationBuilder.getDummyLocation(), false, new VariableLHS[] { lhs });
		final var newSpecification =
				spec != null ? Arrays.copyOf(spec, spec.length + 1) : new Specification[] { modifiesLockSpec };
		final var l = spec != null ? spec.length : 0;
		newSpecification[l] = modifiesLockSpec;
		return new Procedure(proc.getLoc(), proc.getAttributes(), proc.getIdentifier(), proc.getTypeParams(),
				proc.getInParams(), proc.getOutParams(), newSpecification, proc.getBody());
	}

	private AssumeStatement getAssumeStatement() {
		final var negatedLock =
				ExpressionFactory.constructUnaryExpression(mDeclarationBuilder.getDummyLocation(), Operator.LOGICNEG,
						new IdentifierExpression(mDeclarationBuilder.getDummyLocation(), BoogieType.TYPE_BOOL,
								mDeclarationBuilder.getIdentifier(), DeclarationInformation.DECLARATIONINFO_GLOBAL));
		return new AssumeStatement(mDeclarationBuilder.getDummyLocation(), negatedLock);
	}

	private Statement getLockAssignment(final boolean val) {
		final Expression assignment = ExpressionFactory.createBooleanLiteral(null, val);
		final LeftHandSide[] lhs = { mDeclarationBuilder.getLhs() };
		return StatementFactory.constructAssignmentStatement(mDeclarationBuilder.getDummyLocation(), lhs,
				new Expression[] { assignment });
	}

	private List<Statement> processAtomic(final AtomicStatement atomicStatement) {
		final List<Statement> lockedStatements = new ArrayList<>();
		final var compareLock = getAssumeStatement();
		final var setLock = getLockAssignment(true);
		final var compareAndSet =
				new AtomicStatement(mDeclarationBuilder.getDummyLocation(), new Statement[] { compareLock, setLock });
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

	private boolean isAtomic(final Statement statement) {
		return isAtomicBegin(statement) || isAtomicEnd(statement);
	}

	private boolean isAtomicBegin(final Statement statement) {
		if (!(statement instanceof CallStatement)) {
			return false;
		}
		final var call = (CallStatement) statement;
		return call.getMethodName().equals(ATOMIC_BEGIN);
	}

	private boolean isAtomicEnd(final Statement statement) {
		if (!(statement instanceof CallStatement)) {
			return false;
		}
		final var call = (CallStatement) statement;
		return call.getMethodName().equals(ATOMIC_END);
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
		private static final String IDENTIFIER = "atomic_lock";
		private static int SUFFIX = 0;

		private static BoogieType BOOL = BoogieType.TYPE_BOOL;
		private final String mIdentifier;

		private final VariableDeclaration mVariableDeclaration;
		private final ASTType mAstType;
		private final VariableLHS mLhs;
		private final Unit mUnit;

		public DummyVarDeclarationBuilder(final ASTType astType, final Unit unit) {
			mAstType = astType;
			mUnit = unit;
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

		public ILocation getDummyLocation() {
			final var fileName = mUnit.getLoc().getFileName();
			return new BoogieLocation(fileName, -1, -1, -1, -1);
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
