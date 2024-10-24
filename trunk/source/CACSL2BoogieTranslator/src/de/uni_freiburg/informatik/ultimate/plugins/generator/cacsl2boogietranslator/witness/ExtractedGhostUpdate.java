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
import java.util.stream.Stream;

import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTExpressionStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.acsl.parser.ACSLSyntaxErrorException;
import de.uni_freiburg.informatik.ultimate.acsl.parser.Parser;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryModelDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;

/**
 * Witness entry for the update of ghost variables
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ExtractedGhostUpdate implements IExtractedWitnessEntry {
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

	private String getNameOfCalledFunction() {
		final IASTExpression expr;
		if (mMatchedAstNode instanceof IASTExpression) {
			expr = (IASTExpression) mMatchedAstNode;
		} else if (mMatchedAstNode instanceof IASTExpressionStatement) {
			expr = ((IASTExpressionStatement) mMatchedAstNode).getExpression();
		} else {
			return null;
		}
		if (expr instanceof IASTFunctionCallExpression) {
			final IASTExpression function = ((IASTFunctionCallExpression) expr).getFunctionNameExpression();
			if (function instanceof IASTIdExpression) {
				return ((IASTIdExpression) function).getName().toString();
			}
		}
		return null;
	}

	private static List<Statement> annotateAtomicCall(final ILocation loc, final List<Statement> programStatements,
			final List<Statement> ghostUpdate, final String functionName) {
		final List<Statement> result = new ArrayList<>();
		boolean isAnnotated = false;
		for (final Statement st : programStatements) {
			if (isAnnotated || !(st instanceof AtomicStatement)) {
				result.add(st);
				continue;
			}
			final Statement[] atomicBody = ((AtomicStatement) st).getBody();
			if (Arrays.stream(atomicBody).anyMatch(
					x -> x instanceof CallStatement && ((CallStatement) x).getMethodName().equals(functionName))) {
				isAnnotated = true;
				result.add(StatementFactory.constructAtomicStatement(loc,
						Stream.concat(ghostUpdate.stream(), Arrays.stream(atomicBody))));
			} else {
				result.add(st);
			}
		}
		if (!isAnnotated) {
			throw new UnsupportedOperationException("No statement found to annotate with the expected ghost update");
		}
		return result;
	}

	private static List<Statement> annotateFork(final ILocation loc, final List<Statement> programStatements,
			final List<Statement> ghostUpdate) {
		final List<Statement> result = new ArrayList<>();
		boolean isAnnotated = false;
		for (final Statement st : programStatements) {
			if (!isAnnotated && st instanceof ForkStatement) {
				isAnnotated = true;
				result.add(StatementFactory.constructAtomicStatement(loc, ghostUpdate));
			}
			result.add(st);
		}
		if (!isAnnotated) {
			throw new UnsupportedOperationException("No statement found to annotate with the expected ghost update");
		}
		return result;
	}

	@Override
	public ExpressionResult transform(final ILocation loc, final IDispatcher dispatcher,
			final ExpressionResult expressionResult) {
		final ExpressionResult witness = instrument(loc, dispatcher);
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
					.resetStatements(annotateFork(loc, expressionResult.getStatements(), witness.getStatements()))
					.build();
		default:
			throw new UnsupportedOperationException(
					"The following statement is not yet supported for ghost updates: " + loc);
		}
	}
}
