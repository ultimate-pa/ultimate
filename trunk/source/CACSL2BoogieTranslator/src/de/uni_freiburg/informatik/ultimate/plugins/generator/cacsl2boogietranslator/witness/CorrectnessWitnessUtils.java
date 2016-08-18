/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.ASTGenericVisitor;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDoStatement;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;
import org.eclipse.cdt.core.dom.ast.IASTWhileStatement;

/**
 * This class collects helpers that can be used to navigate the CDT AST.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class CorrectnessWitnessUtils {

	public static IASTStatement findSuccessorStatement(final IASTStatement stmt) {
		if (stmt == null || stmt.getParent() == null) {
			return null;
		}

		IASTNode parent = stmt.getParent();
		while (parent != null) {
			if (parent instanceof IASTCompoundStatement) {
				break;
			}
			if (parent instanceof IASTStatement) {
				parent = parent.getParent();
			} else {
				break;
			}
		}

		if (parent == null) {
			return null;
		}

		IASTStatement successorStatement = null;
		if (parent instanceof IASTCompoundStatement) {
			final IASTCompoundStatement compound = (IASTCompoundStatement) parent;
			final IASTStatement[] stmts = compound.getStatements();
			for (int i = 0; i < stmts.length; ++i) {
				if (!stmt.equals(stmts[i])) {
					continue;
				}
				if (i < stmts.length - 1) {
					// found successor in compound statement
					successorStatement = stmts[i + 1];
				} else {
					// need to find successor of compound statement
					successorStatement = findSuccessorStatement(compound);
				}
				break;
			}
		}

		if (successorStatement instanceof IASTCompoundStatement) {
			final IASTCompoundStatement succComp = (IASTCompoundStatement) successorStatement;
			if (succComp.getStatements().length == 0) {
				// if this statement has no children, we need its successor
				successorStatement = findSuccessorStatement(succComp);
			}
		}

		if (successorStatement != null) {
			assert !successorStatement.equals(stmt);
			return successorStatement;
		}

		throw new UnsupportedOperationException("Did not think that far");
	}

	public static IASTStatement findBranchingSuccessorStatement(final boolean trueOrFalseBranch,
			final IASTStatement statement) {
		if (statement instanceof IASTForStatement) {
			final IASTForStatement forstmt = (IASTForStatement) statement;
			return trueOrFalseBranch ? forstmt.getBody() : findSuccessorStatement(statement);
		} else if (statement instanceof IASTIfStatement) {
			final IASTIfStatement ifstmt = (IASTIfStatement) statement;
			return trueOrFalseBranch ? ifstmt.getThenClause() : ifstmt.getElseClause();
		} else if (statement instanceof IASTDoStatement) {
			final IASTDoStatement dostmt = (IASTDoStatement) statement;
			return trueOrFalseBranch ? dostmt.getBody() : findSuccessorStatement(statement);
		} else if (statement instanceof IASTWhileStatement) {
			final IASTWhileStatement whilestmt = (IASTWhileStatement) statement;
			return trueOrFalseBranch ? whilestmt.getBody() : findSuccessorStatement(statement);
		}
		throw new UnsupportedOperationException("statement " + statement + " is not a branching statement");
	}

	public static IASTDeclaration findScope(final IASTNode current) {
		IASTNode parent = current.getParent();
		while (parent != null) {
			if (parent instanceof IASTFunctionDefinition) {
				return (IASTDeclaration) parent;
			}
			if (parent instanceof IASTTranslationUnit) {
				return null;
			}
			parent = parent.getParent();
		}
		return null;
	}

	public static boolean isContainedInSubtree(final IASTNode candidate, final IASTNode possibleParent) {
		final SubtreeChecker sc = new SubtreeChecker(candidate);
		possibleParent.accept(sc);
		return sc.isContainedInSubtree();
	}

	public static Set<IASTStatement> findDesiredType(final IASTNode node, final Collection<Class<?>> desiredTypes) {
		return new DesiredTypeExtractor(desiredTypes).run(node);
	}

	private static final class DesiredTypeExtractor extends ASTGenericVisitor {
		private Set<IASTStatement> mStatements;
		private final Collection<Class<?>> mDesiredClasses;

		public DesiredTypeExtractor(final Collection<Class<?>> desiredClasses) {
			super(true);
			mDesiredClasses = desiredClasses;
		}

		public Set<IASTStatement> run(final IASTNode subtreeRoot) {
			mStatements = new HashSet<>();
			subtreeRoot.accept(this);
			return mStatements;
		}

		@Override
		public int visit(final IASTStatement statement) {
			if (mDesiredClasses.stream().anyMatch(a -> a.isAssignableFrom(statement.getClass()))) {
				mStatements.add(statement);
				return PROCESS_SKIP;
			}
			return PROCESS_CONTINUE;
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class SubtreeChecker extends ASTGenericVisitor {

		private final IASTNode mCandidate;
		private boolean mIsContainedInSubtree;

		public SubtreeChecker(final IASTNode candidate) {
			super(true);
			mCandidate = candidate;
			mIsContainedInSubtree = false;
		}

		public boolean isContainedInSubtree() {
			return mIsContainedInSubtree;
		}

		@Override
		protected int genericVisit(final IASTNode child) {
			if (mIsContainedInSubtree) {
				return PROCESS_ABORT;
			}
			if (child == mCandidate) {
				mIsContainedInSubtree = true;
				return PROCESS_ABORT;
			}
			return PROCESS_CONTINUE;
		}
	}
}
