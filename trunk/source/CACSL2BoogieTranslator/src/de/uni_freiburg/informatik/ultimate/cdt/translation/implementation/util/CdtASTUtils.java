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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
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
public final class CdtASTUtils {

	private CdtASTUtils() {
		// do not instantiate a utility class
	}

	/**
	 * Given an {@link IASTStatement}, find the next non-empty {@link IASTStatement} with regard to the control-flow of
	 * the C program.
	 *
	 * @param stmt
	 *            The statement for which you want to find a control-flow successor.
	 * @return The control-flow successor of <code>stmt</code> or null if
	 *         <ul>
	 *         <li>stmt has no successor (i.e., its the last statement of the program),
	 *         <li>stmt is null,
	 *         <li>stmt has no parent, i.e., its disconnected from the AST.
	 *         </ul>
	 *
	 */
	public static IASTStatement findSuccessorStatement(final IASTStatement stmt) {
		if (stmt == null || stmt.getParent() == null) {
			return null;
		}
		final IASTNode parent = stmt.getParent();
		if (!(parent instanceof IASTStatement)) {
			// this is sad, we would have to resolve interprocedural successors
			return null;
		}
		final IASTNode[] children = parent.getChildren();
		for (int i = 0; i < children.length - 1; ++i) {
			if (children[i].equals(stmt)) {
				// this is the current stmt; the next child must be the successor
				return getFirstOrSuccessorStatement((IASTStatement) children[i + 1]);
			}
		}
		// if we made it past this point, we should be the last child
		assert children[children.length - 1].equals(stmt);
		// now we have to find the successor of our parent
		return findSuccessorStatement((IASTStatement) parent);
	}

	/**
	 * Find the next non-empty successor statement of a branching statement for which you know whether the condition
	 * evaluates to true or to false.
	 *
	 * @param trueOrFalseBranch
	 *            true if the condition evaluates to true, false if the condition evaluates to false.
	 * @param statement
	 *            the branching statement
	 * @return the next non-empty successor statement of <code>statement</code>
	 * @see #findSuccessorStatement(IASTStatement)
	 */
	public static IASTStatement findBranchingSuccessorStatement(final boolean trueOrFalseBranch,
			final IASTStatement statement) {
		if (statement instanceof IASTForStatement) {
			final IASTForStatement forstmt = (IASTForStatement) statement;
			return trueOrFalseBranch ? getFirstOrSuccessorStatement(forstmt.getBody())
					: findSuccessorStatement(statement);
		} else if (statement instanceof IASTIfStatement) {
			final IASTIfStatement ifstmt = (IASTIfStatement) statement;
			return trueOrFalseBranch ? getFirstOrSuccessorStatement(ifstmt.getThenClause())
					: getFirstOrSuccessorStatement(ifstmt.getElseClause());
		} else if (statement instanceof IASTDoStatement) {
			final IASTDoStatement dostmt = (IASTDoStatement) statement;
			return trueOrFalseBranch ? getFirstOrSuccessorStatement(dostmt.getBody())
					: findSuccessorStatement(statement);
		} else if (statement instanceof IASTWhileStatement) {
			final IASTWhileStatement whilestmt = (IASTWhileStatement) statement;
			return trueOrFalseBranch ? getFirstOrSuccessorStatement(whilestmt.getBody())
					: findSuccessorStatement(statement);
		}
		throw new IllegalArgumentException("statement " + statement + " is not a branching statement");
	}

	public static boolean isBranchingStatement(final IASTStatement statement) {
		return statement instanceof IASTForStatement || statement instanceof IASTIfStatement
				|| statement instanceof IASTDoStatement || statement instanceof IASTWhileStatement;
	}

	/**
	 * If stmt is a {@link IASTCompoundStatement}, returns the first non-compound statement in the body, or, the
	 * successor of the compound statement if it is empty, or the statement itself if it is not a compound statement.
	 *
	 * @param stmt
	 * @return
	 */
	public static IASTStatement getFirstOrSuccessorStatement(final IASTStatement stmt) {
		if (stmt instanceof IASTCompoundStatement) {
			return getFirstOrSuccessorStatement((IASTCompoundStatement) stmt);
		}
		return stmt;
	}

	/**
	 * Search for the first {@link IASTStatement} that encloses this {@link IASTNode}, i.e., the first parent that is an
	 * IASTStatement.
	 *
	 * @param node
	 *            The enclosed node.
	 * @return The first enclosing statement or null if there is no such statement.
	 */
	public static IASTStatement getEnclosingStatement(final IASTNode node) {
		if (node == null || node.getParent() == null) {
			return null;
		}
		IASTNode parent = node.getParent();
		while (parent != null) {
			if (parent instanceof IASTStatement) {
				return (IASTStatement) parent;
			}
			parent = parent.getParent();
		}
		return null;
	}

	private static IASTStatement getFirstOrSuccessorStatement(final IASTCompoundStatement cmpStmt) {
		final IASTStatement[] children = cmpStmt.getStatements();
		return children.length == 0 ? findSuccessorStatement(cmpStmt) : getFirstOrSuccessorStatement(children[0]);
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

	/**
	 * Checks whether <code>canidate</code> is a transitive child of <code>possibleParent</code> or not.
	 * 
	 * @param candidate
	 *            The possible child.
	 * @param possibleParent
	 *            The possible parent.
	 * 
	 * @return true iff candidate is a transitive child of possibleParent.
	 */
	public static boolean isContainedInSubtree(final IASTNode candidate, final IASTNode possibleParent) {
		final SubtreeChecker sc = new SubtreeChecker(candidate);
		possibleParent.accept(sc);
		return sc.isContainedInSubtree();
	}

	/**
	 * Find the first {@link IASTNode} that is a parent to all of the provided nodes.
	 * 
	 * @param nodes
	 *            a collection of nodes for which a common parent should be found.
	 * @return The first IASTNode that is a parent to all the provided nodes or the node itself if only one node is
	 *         provided, or null if there are no nodes or there is no common parent to all nodes.
	 */
	public static IASTNode findCommonParent(final Collection<IASTNode> nodes) {
		if (nodes == null || nodes.isEmpty()) {
			return null;
		}
		assert nodes.stream().noneMatch(Objects::isNull);
		if (nodes.size() == 1) {
			return nodes.iterator().next();
		}

		final List<Set<IASTNode>> pathsToRoot = new ArrayList<>();
		nodes.stream().forEach(a -> pathsToRoot.add(getParentNodes(a)));
		IASTNode possibleParent = nodes.iterator().next();
		while (possibleParent != null) {
			final IASTNode testedParent = possibleParent;
			if (pathsToRoot.stream().allMatch(a -> a.contains(testedParent))) {
				return testedParent;
			}
			possibleParent = possibleParent.getParent();
		}

		return null;
	}

	private static Set<IASTNode> getParentNodes(final IASTNode node) {
		final Set<IASTNode> rtr = new LinkedHashSet<>();
		rtr.add(node);
		IASTNode parent = node.getParent();
		while (parent != null) {
			rtr.add(parent);
			parent = parent.getParent();
		}
		return rtr;
	}

	public static Set<IASTStatement> findDesiredType(final IASTNode node, final Collection<Class<?>> desiredTypes) {
		if (node == null) {
			return Collections.emptySet();
		}
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
