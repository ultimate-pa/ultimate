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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class AtomicsToLocks extends BoogieTransformer implements IUnmanagedObserver {
	// Options result in different outputs
	private static final boolean ATOMIC_GUARD_STATEMENTS = true;
	private static final boolean OMIT_ATOMICS_WITHOUT_LOOP = false;

	private static final String ATOMIC_BEGIN = "__VERIFIER_atomic_begin";
	private static final String ATOMIC_END = "__VERIFIER_atomic_end";

	private final ILogger mLogger;
	private DummyVarDeclarationBuilder mDeclarationBuilder;
	private Statement mInitStatement;
	private BoogieDeclarations mBoogieDeclarations;
	private boolean mContainsAtomic;
	private final Set<String> mModifiesLock = new HashSet<>();

	protected AtomicsToLocks(final BoogiePreprocessorBacktranslator translator,
			final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * The process function. Called by the tool-chain and gets a node of the graph as parameter. This function descends
	 * to the unit node and then searches for all atomic blocks and replaces them with lock-based code
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof final Unit unit) {
			mBoogieDeclarations = new BoogieDeclarations(unit, mLogger);
			final Map<Procedure, Statement[]> procedureToNewBlock = new HashMap<>();
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
				final var identifier = proc.getIdentifier();
				final var impl = mBoogieDeclarations.getProcImplementation().get(identifier);
				if (impl == null || !impl.equals(proc) || identifier.equals(SFO.INIT)) {
					// If there is no implementation or proc is the specification nothing needs to be replaced
					newDeclarations.add(proc);
				} else if (proc.getBody() != null) {
					final var newBody = replaceAtomics(proc);
					procedureToNewBlock.put(proc, newBody);
					newDeclarations.add(proc);
				}
			}
			if (mModifiesLock.isEmpty()) {
				return false;
			}
			setNewBodies(procedureToNewBlock);
			initializeLockInUnit();
			getNewSpecifications(newDeclarations);
			unit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
			return false;
		}
		return true;
	}

	/**
	 * Recursively search for atomic blocks in the procedure and replace them by locks
	 *
	 * @param proc
	 *            Procedure in which atomics should be replaced
	 */
	private Statement[] replaceAtomics(final Procedure proc) {
		final Body body = proc.getBody();

		mContainsAtomic = false;
		final var newStatements = processStatements(body.getBlock());
		if (mContainsAtomic) {
			mModifiesLock.add(proc.getIdentifier());
			mContainsAtomic = false;
		}
		return newStatements;
	}

	@Override
	protected Statement[] processStatements(final Statement[] statements) {
		final var assume = getAssumeStatement();
		final List<Statement> statementList = new ArrayList<>();
		for (int i = 0; i < statements.length; i++) {
			final var statement = statements[i];
			if (statement instanceof final AtomicStatement atomicstmt) {
				final var lockedSection = atomicToLocked(atomicstmt.getBody());
				statementList.addAll(lockedSection);
			} else if (isAtomicBegin(statement)) {
				statementList.addAll(computeAtomicBlock(Arrays.copyOfRange(statements, i, statements.length)));
				break;
			} else {
				final var processedStatement = processStatement(statement);
				statementList.addAll(getGuardedStatement(processedStatement, assume));
			}

		}
		return statementList.toArray(new Statement[statementList.size()]);
	}

	private List<Statement> getGuardedStatement(final Statement statement, final AssumeStatement assumeStatement) {
		final var guardedStmt = new ArrayList<Statement>();
		if ((statement instanceof final Label) || (statement == mInitStatement)
				|| (statement instanceof BreakStatement)) {
			// We don't need an assume infront of a label or the initial lock assignment
			guardedStmt.add(statement);
		} else if (statement instanceof IfStatement || isLoop(statement) || !ATOMIC_GUARD_STATEMENTS) {
			guardedStmt.add(assumeStatement);
			guardedStmt.add(statement);
		} else {
			final var atomicGuard = new AtomicStatement(mDeclarationBuilder.getDummyLocation(),
					new Statement[] { assumeStatement, statement });
			guardedStmt.add(atomicGuard);
		}
		return guardedStmt;
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		Statement newStatement = null;
		// TODO: What about assert, assignment, havoc?
		if (statement instanceof final IfStatement ifstmt) {
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

	/**
	 * Adjust the specifications of all procedures that modify the lock variable
	 *
	 * @param declarations
	 *            All declarations of Unit
	 */
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

	private void setNewBodies(final Map<Procedure, Statement[]> procedureToNewBlock) {
		for (final Entry<Procedure, Statement[]> entry : procedureToNewBlock.entrySet()) {
			final var proc = entry.getKey();
			final var block = entry.getValue();
			proc.getBody().setBlock(block);
		}
	}

	/**
	 * Adds a ModifiesSpecification for the variable left-hand-side to the procedure
	 *
	 * @param proc
	 *            Procedure that modifies the variable
	 * @param lhs
	 *            Left-Hand-Side of the variable
	 * @return Procedure with modified specification
	 */
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

	private DummyVarDeclarationBuilder constructDeclarationBuilder(final Unit unit) {
		final String typeName = "bool";
		final NamedType astType = new NamedType(null, BoogieType.TYPE_BOOL, typeName, new ASTType[0]);
		return new DummyVarDeclarationBuilder(astType, unit);
	}

	/**
	 * Initializes the lock variable in the program with root unit if there exists a procedure named ULTIMATE.init or
	 * ULTIMATE.start in the list of declarations.
	 */
	private void initializeLockInUnit() {
		Procedure initProc = null;
		Procedure startProc = null;
		for (final Procedure procedure : mBoogieDeclarations.getProcImplementation().values()) {
			if (procedure.getIdentifier().equals(SFO.INIT)) {
				initProc = procedure;
				break;
			}
			if (procedure.getIdentifier().equals(SFO.START)) {
				startProc = procedure;
			}
		}
		assert (initProc != null) || (startProc != null)
				: "The setting replace atomics requires a procedure named " + SFO.INIT + " or " + SFO.START;
		if (initProc != null) {
			initializeLockInProc(initProc);
		} else {
			initializeLockInProc(startProc);
		}
	}

	/**
	 * Initializes the lock variable in procedure to the boolean value false
	 *
	 * @param procedure
	 *            Procedure in which the lock should be initialized
	 */
	private void initializeLockInProc(final Procedure procedure) {
		final var body = procedure.getBody();
		final var block = body.getBlock();
		final var newBlock = addInitStatement(block);
		body.setBlock(newBlock);
		mModifiesLock.add(procedure.getIdentifier());
	}

	/**
	 * Add assignment of the lock variable to false to the list of statements on index 0
	 *
	 * @param blockStatements
	 *            List of statements in which the assignment should be added
	 * @return List with additional assignment of lock
	 */
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

	/**
	 * Converts an atomic statement into a block containing the body of the atomic statement enclosed by assignments of
	 * the lock variable, first to true and at the end of the block to false. All nested atomics get removed from the
	 * body of the original statement
	 */
	private List<Statement> atomicToLocked(final Statement[] atomicBlock) {
		if (!atomicContainsLoop(atomicBlock) && OMIT_ATOMICS_WITHOUT_LOOP) {
			return Arrays.asList(atomicBlock);
		}
		mContainsAtomic = true;
		final List<Statement> lockedStatements = new ArrayList<>();
		final var compareAndSet = getAtomicCompareAndSet(true);
		lockedStatements.add(compareAndSet);
		final var noNestedAtomics = removeAtomics(atomicBlock);
		lockedStatements.addAll(noNestedAtomics);
		lockedStatements.add(getLockAssignment(false));
		return lockedStatements;
	}

	private AtomicStatement getAtomicCompareAndSet(final boolean val) {
		final var compareLock = getAssumeStatement();
		final var setLock = getLockAssignment(val);
		return new AtomicStatement(mDeclarationBuilder.getDummyLocation(), new Statement[] { compareLock, setLock });
	}

	/**
	 * Remove all atomic blocks (atomic{...} and __VERIFIER_ATOMIC calls) from the statements
	 */
	private List<Statement> removeAtomics(final Statement[] statements) {
		final List<Statement> statementList = new ArrayList<>();
		for (final Statement statement : statements) {
			final var noNestedAtomics = removeAtomics(statement);
			statementList.addAll(noNestedAtomics);
		}
		return statementList;
	}

	/**
	 * Recursively remove atomic blocks from the statement and replace them with their bodies
	 */
	private List<Statement> removeAtomics(final Statement statement) {
		Statement newStatement = statement;
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
		} else if (statement instanceof final CallStatement callStatement) {
			// Remove nested calls to __VERIFIER_atomic
			if (isAtomic(callStatement)) {
				return List.of();
			}
		} else if (statement instanceof final AtomicStatement atomicStatement) {
			return removeAtomics(atomicStatement.getBody());
		} else {
			return List.of(statement);
		}
		ModelUtils.copyAnnotations(statement, newStatement);
		return List.of(newStatement);
	}

	/**
	 * Compute the list of statements between two calls of __VERIFIER_atomic_begin() and __VERIFIER_atomic_end(). Fails
	 * if multiple of such calls are nested.
	 *
	 * @param statements
	 *            List of statements that contains calls to __VERIFIER_atomic_begin() and __VERIFIER_atomic_end()
	 * @return New list of statements where the atomic block is replaced with assignments to lock
	 */
	private List<Statement> computeAtomicBlock(final Statement[] statements) {
		assert isAtomicBegin(statements[0]) : "Block is not atomic";
		final List<Statement> atomicBlock = new ArrayList<>();
		final List<Statement> remainingStatements = new ArrayList<>();
		int atomicEndIdx = -1;
		for (int i = 0; i < statements.length; i++) {
			final var statement = statements[i];
			if (isAtomicBegin(statement)) {
				// TODO: Remove nested atomics
				assert i == 0 : "Nested __VERIFIER_atomic calls are not supported by the translation of atomics "
						+ "into lock-based blocks in the BoogiePreprocessor!";
			}
			if (isEndOfAtomicBlock(statement)) {
				atomicBlock.add(statement);
				atomicEndIdx = i;
				break;
			}
			atomicBlock.add(statement);
		}
		// Assume implicit atomic end at the end of the code block
		atomicEndIdx = atomicEndIdx == -1 ? statements.length : atomicEndIdx;

		// Add all remaining statements after the atomic ends
		for (int j = atomicEndIdx + 1; j < statements.length; j++) {
			remainingStatements.add(statements[j]);
		}
		final List<Statement> replacedBlock = new ArrayList<>();
		if (!OMIT_ATOMICS_WITHOUT_LOOP || atomicContainsLoop(atomicBlock.toArray(new Statement[0]))) {
			mContainsAtomic = true;
			final var replaced = replaceVerifierAtomics(atomicBlock, false).getFirst();
			replacedBlock.addAll(replaced);
		} else {
			replacedBlock.add(getAssumeStatement());
			replacedBlock.addAll(atomicBlock);
		}
		replacedBlock.addAll(Arrays.asList(processStatements(remainingStatements.toArray(new Statement[0]))));
		return replacedBlock;
	}

	private Pair<List<Statement>, Boolean> replaceVerifierAtomics(final List<Statement> block, boolean atomicEnded) {
		final List<Statement> newStatements = new ArrayList<>();
		final var compareAndSet = getAtomicCompareAndSet(true);
		final var lockToFalse = getLockAssignment(false);
		for (int i = 0; i < block.size(); i++) {
			final var statement = block.get(i);
			Statement newStatement = statement;
			if (atomicEnded) {
				final var remainingStatements = block.subList(i, block.size()).toArray(new Statement[0]);
				final var processedStatements = processStatements(remainingStatements);
				newStatements.addAll(Arrays.asList(processedStatements));
				break;
			} else if (statement instanceof final CallStatement callStatement) {
				if (isAtomicBegin(callStatement)) {
					newStatement = compareAndSet;
				} else if (isAtomicEnd(callStatement)) {
					newStatement = lockToFalse;
					atomicEnded = true;
				} else {
					newStatement = statement;
				}
			} else if (statement instanceof final WhileStatement whileStatement) {
				final var oldBody = Arrays.asList(whileStatement.getBody());
				final Pair<List<Statement>, Boolean> bodyPair = replaceVerifierAtomics(oldBody, atomicEnded);
				final var newBody = bodyPair.getFirst();
				atomicEnded = bodyPair.getSecond();
				newStatement = new WhileStatement(whileStatement.getLoc(), whileStatement.getCondition(),
						whileStatement.getInvariants(), newBody.toArray(new Statement[0]));
			} else if (statement instanceof final IfStatement ifStatement) {
				final Expression cond = ifStatement.getCondition();
				final Statement[] thens = ifStatement.getThenPart();
				final Pair<List<Statement>, Boolean> thenPair =
						replaceVerifierAtomics(Arrays.asList(thens), atomicEnded);
				final Statement[] newThens = thenPair.getFirst().toArray(new Statement[0]);
				final Statement[] elses = ifStatement.getElsePart();
				final Pair<List<Statement>, Boolean> elsePair =
						replaceVerifierAtomics(Arrays.asList(elses), atomicEnded);
				final Statement[] newElses = elsePair.getFirst().toArray(new Statement[0]);
				atomicEnded = thenPair.getSecond() && elsePair.getSecond();
				newStatement = new IfStatement(ifStatement.getLocation(), cond, newThens, newElses);
			}
			newStatements.add(newStatement);
		}
		return new Pair<>(newStatements, atomicEnded);
	}

	private boolean isAtomic(final Statement statement) {
		return isAtomicBegin(statement) || isAtomicEnd(statement);
	}

	private boolean isAtomicBegin(final Statement statement) {
		return isCallTo(statement, ATOMIC_BEGIN);
	}

	private boolean isAtomicEnd(final Statement statement) {
		return isCallTo(statement, ATOMIC_END);
	}

	private boolean isCallTo(final Statement statement, final String name) {
		if (!(statement instanceof CallStatement)) {
			return false;
		}
		final var call = (CallStatement) statement;
		return call.getMethodName().equals(name);
	}

	private boolean isEndOfAtomicBlock(final Statement[] statements) {
		for (final Statement statement : statements) {
			if (isEndOfAtomicBlock(statement)) {
				return true;
			}
		}
		return false;
	}

	private boolean isEndOfAtomicBlock(final Statement statement) {
		if (isAtomicEnd(statement)) {
			return true;
		} else if (statement instanceof final WhileStatement whileStatement) {
			return isEndOfAtomicBlock(whileStatement.getBody());
		} else if (statement instanceof final IfStatement ifStatement) {
			final var then = ifStatement.getThenPart();
			final var elsePart = ifStatement.getElsePart();
			final var thenContainsEnd = isEndOfAtomicBlock(then);
			final var elseContainsEnd = isEndOfAtomicBlock(elsePart);
			// Atomic block only ends if then-part and else-part both contain an atomic end
			return thenContainsEnd && elseContainsEnd;
		}
		return false;
	}

	private boolean atomicContainsLoop(final Statement[] body) {
		for (final Statement statement : body) {
			if (!isAtomic(statement) && isLoop(statement)) {
				return true;
			} else if (statement instanceof final IfStatement ifStatement) {
				final var thens = ifStatement.getThenPart();
				final var elses = ifStatement.getElsePart();
				return atomicContainsLoop(thens) || atomicContainsLoop(elses);
			}
		}
		return false;
	}

	private boolean isLoop(final Statement statement) {
		return (statement instanceof WhileStatement || statement instanceof CallStatement
				|| statement instanceof ForkStatement || statement instanceof GotoStatement || statement instanceof JoinStatement);
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
		private static final int SUFFIX = 0;

		private static final BoogieType BOOL = BoogieType.TYPE_BOOL;
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
