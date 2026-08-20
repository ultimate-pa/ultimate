/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.witness;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Predicate;
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTDeclarationStatement;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Witness entry for the update of ghost variables
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedGhostUpdate implements IExtractedWitnessEntry {
	private static final List<Integer> ASSIGNMENT_OPERATORS = List.of(IASTBinaryExpression.op_assign,
			IASTBinaryExpression.op_multiplyAssign, IASTBinaryExpression.op_divideAssign,
			IASTBinaryExpression.op_moduloAssign, IASTBinaryExpression.op_plusAssign,
			IASTBinaryExpression.op_minusAssign, IASTBinaryExpression.op_shiftLeftAssign,
			IASTBinaryExpression.op_shiftRightAssign, IASTBinaryExpression.op_binaryAndAssign,
			IASTBinaryExpression.op_binaryXorAssign, IASTBinaryExpression.op_binaryOrAssign);

	private final IASTNode mMatchedAstNode;
	private final String mStatement;

	public ExtractedGhostUpdate(final String variable, final String value, final IASTNode match) {
		mStatement = String.format("%s = %s;", variable, value);
		mMatchedAstNode = match;
	}

	private int getStartline() {
		return mMatchedAstNode.getFileLocation().getStartingLineNumber();
	}

	private int getEndline() {
		return mMatchedAstNode.getFileLocation().getEndingLineNumber();
	}

	public IASTNode getRelatedAstNode() {
		return mMatchedAstNode;
	}

	@Override
	public String toString() {
		return "ghost_update [L" + getStartline() + "-L" + getEndline() + "] " + mStatement;
	}

	protected ExpressionResult instrument(final ILocation loc, final IDispatcher dispatcher) {
		ACSLNode acslNode = null;
		try {
			acslNode = Parser.parseComment("lstart\n ghost " + mStatement, getStartline(), 1);
		} catch (final ACSLSyntaxErrorException e) {
			throw new UnsupportedSyntaxException(loc, e.getMessageText());
		} catch (final Exception e) {
			throw new AssertionError(e);
		}
		return (ExpressionResult) dispatcher.dispatch(acslNode, mMatchedAstNode);
	}

	private IASTExpression getExpression() {
		switch (mMatchedAstNode) {
		case final IASTExpression expr:
			return expr;
		case final IASTExpressionStatement exprSt:
			return exprSt.getExpression();
		default:
			return null;
		}
	}

	private String getNameOfCalledFunction() {
		if (getExpression() instanceof final IASTFunctionCallExpression call
				&& call.getFunctionNameExpression() instanceof final IASTIdExpression id) {
			return id.getName().toString();
		}
		return null;
	}

	private static List<Statement> annotateLastOccurence(final ILocation loc, final List<Statement> programStatements,
			final List<Statement> ghostUpdate, final Predicate<Statement> predicate, final boolean makeAtomic) {
		final List<Statement> result = new ArrayList<>(programStatements);
		boolean isAnnotated = false;
		for (int i = programStatements.size() - 1; i >= 0; i--) {
			final Statement current = programStatements.get(i);
			if (predicate.test(current)) {
				isAnnotated = true;
				if (makeAtomic) {
					// Create an atomic block with the matching statement and the ghost update
					// Try to avoid nested atomic statements here
					final Stream<Statement> currentStatements =
							current instanceof final AtomicStatement atomic ? Arrays.stream(atomic.getBody())
									: Stream.of(current);
					result.set(i, StatementFactory.constructAtomicStatement(loc,
							Stream.concat(currentStatements, ghostUpdate.stream())));
				} else {
					// Insert the ghost update just before the matching statement
					result.add(i, StatementFactory.constructAtomicStatement(loc, ghostUpdate));
				}
				break;
			}
		}
		if (!isAnnotated) {
			throw new UnsupportedOperationException("No statement found to annotate with the expected ghost update");
		}
		return result;
	}

	private static boolean isAtomicCall(final Statement st, final String functionName) {
		return st instanceof final AtomicStatement atomic && Arrays.stream(atomic.getBody())
				.anyMatch(x -> x instanceof CallStatement && ((CallStatement) x).getMethodName().equals(functionName));
	}

	private static List<Statement> annotateAtomicCall(final ILocation loc, final List<Statement> programStatements,
			final List<Statement> ghostUpdate, final String functionName) {
		return annotateLastOccurence(loc, programStatements, ghostUpdate, x -> isAtomicCall(x, functionName), true);
	}

	private boolean isAssignmentOrMemoryWrite(final Statement st) {
		return st instanceof AssignmentStatement
				|| (st instanceof final CallStatement call && call.getMethodName().startsWith(SFO.WRITE_PREFIX));
	}

	private boolean isAssignment() {
		return (getExpression() instanceof final IASTBinaryExpression binEx
				&& ASSIGNMENT_OPERATORS.contains(binEx.getOperator()))
				|| mMatchedAstNode instanceof IASTDeclarationStatement;
	}

	@Override
	public ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult) {
		final ExpressionResult witness = instrument(loc, dispatcher);
		if (isAssignment()) {
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateLastOccurence(loc, expressionResult.getStatements(),
							witness.getStatements(), this::isAssignmentOrMemoryWrite, true))
					.build();
		}
		final String functionName = getNameOfCalledFunction();
		if (functionName == null) {
			// TODO: Support other statements, also not only function calls
			throw new UnsupportedOperationException(
					"The following statement is not yet supported for ghost updates: " + loc);
		}
		switch (functionName) {
		case "__VERIFIER_atomic_begin":
			// Insert the ghost update after the begin of the atomic block to ensure that it is executed atomically.
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValue(witness).build();
		case "__VERIFIER_atomic_end":
			// Insert the ghost update before the end of the atomic block to ensure that it is executed atomically.
			return new ExpressionResultBuilder(witness).addAllExceptLrValue(expressionResult).build();
		case "pthread_mutex_lock":
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateAtomicCall(loc, expressionResult.getStatements(), witness.getStatements(),
							MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName()))
					.build();
		case "pthread_mutex_unlock":
		case "pthread_cond_wait":
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateAtomicCall(loc, expressionResult.getStatements(), witness.getStatements(),
							MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_UNLOCK.getName()))
					.build();
		case "pthread_rwlock_rdlock":
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateAtomicCall(loc, expressionResult.getStatements(), witness.getStatements(),
							MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_READLOCK.getName()))
					.build();
		case "pthread_rwlock_wrlock":
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateAtomicCall(loc, expressionResult.getStatements(), witness.getStatements(),
							MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_WRITELOCK.getName()))
					.build();
		case "pthread_rwlock_unlock":
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateAtomicCall(loc, expressionResult.getStatements(), witness.getStatements(),
							MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_UNLOCK.getName()))
					.build();
		case "pthread_create":
			// Make the ghost update itself atomic and insert it just before the fork.
			// TODO: Maybe we should do this atomically, but the CFG builder crashes for that case
			// We are not sure, if this does have any different semantics.
			return new ExpressionResultBuilder(expressionResult).addAllExceptLrValueAndStatements(witness)
					.resetStatements(annotateLastOccurence(loc, expressionResult.getStatements(),
							witness.getStatements(), ForkStatement.class::isInstance, false))
					.build();
		default:
			throw new UnsupportedOperationException(
					"The following statement is not yet supported for ghost updates: " + loc);
		}
	}
}
