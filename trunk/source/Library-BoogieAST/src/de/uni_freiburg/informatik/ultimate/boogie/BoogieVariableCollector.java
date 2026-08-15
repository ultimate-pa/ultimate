/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE BoogieAST Library.
 *
 * The ULTIMATE BoogieAST Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieAST Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieAST Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieAST Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieAST Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ParentEdge;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Project;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;

/**
 * Utility class to collect the variables occurring (as identifier expressions, or in left-hand-sides) in a Boogie AST.
 */
public class BoogieVariableCollector extends BoogieVisitor {
	private final boolean mIgnoreOldNonOldContext;
	private final boolean mIgnoreLHS;

	private final SequencedSet<VariableOccurrence> mResult = new LinkedHashSet<>();
	private boolean mInOldContext = false;

	public BoogieVariableCollector(final BoogieASTNode node) {
		this(node, false, false);
	}

	public BoogieVariableCollector(final BoogieASTNode node, final boolean ignoreOldNonOldContext,
			final boolean ignoreLHS) {
		mIgnoreOldNonOldContext = ignoreOldNonOldContext;
		mIgnoreLHS = ignoreLHS;
		process(node);
	}

	public BoogieVariableCollector(final Collection<? extends BoogieASTNode> nodes, final boolean ignoreOldNonOldContext,
			final boolean ignoreLHS) {
		mIgnoreOldNonOldContext = ignoreOldNonOldContext;
		mIgnoreLHS = ignoreLHS;
		for (final BoogieASTNode node : nodes) {
			process(node);
		}
	}

	public SequencedSet<VariableOccurrence> collectedOccurences() {
		return mResult;
	}

	public Stream<VariableOccurrence> globalVariables() {
		return mResult.stream().filter(occ -> occ.declarationInformation().getStorageClass() == StorageClass.GLOBAL);
	}

	public boolean usesGlobalVariables() {
		return globalVariables().findAny().isPresent();
	}

	public Stream<IdentifierExpressionOccurrence> globalVariablesRead() {
		return mResult.stream()
				.filter(occ -> occ instanceof IdentifierExpressionOccurrence
						&& occ.declarationInformation().getStorageClass() == StorageClass.GLOBAL)
				.map(occ -> (IdentifierExpressionOccurrence) occ);
	}

	public boolean readsGlobalVariables() {
		return globalVariablesRead().findAny().isPresent();
	}

	public Stream<LeftHandSideOccurrence> globalVariablesAssigned() {
		return mResult.stream()
				.filter(occ -> occ instanceof LeftHandSideOccurrence
						&& occ.declarationInformation().getStorageClass() == StorageClass.GLOBAL)
				.map(occ -> (LeftHandSideOccurrence) occ);
	}

	public boolean assignsGlobalVariables() {
		return globalVariablesAssigned().findAny().isPresent();
	}

	public Stream<VariableOccurrence> nonGlobalVariables() {
		return mResult.stream().filter(occ -> occ.declarationInformation().getStorageClass() == StorageClass.GLOBAL);
	}

	public boolean usesNonGlobalVariables() {
		return nonGlobalVariables().findAny().isPresent();
	}

	public Stream<IdentifierExpressionOccurrence> nonGlobalVariablesRead() {
		return mResult.stream()
				.filter(occ -> occ instanceof IdentifierExpressionOccurrence
						&& occ.declarationInformation().getStorageClass() == StorageClass.GLOBAL)
				.map(occ -> (IdentifierExpressionOccurrence) occ);
	}

	public boolean readsNonGlobalVariables() {
		return nonGlobalVariablesRead().findAny().isPresent();
	}

	public Stream<LeftHandSideOccurrence> nonGlobalVariablesAssigned() {
		return mResult.stream()
				.filter(occ -> occ instanceof LeftHandSideOccurrence
						&& occ.declarationInformation().getStorageClass() == StorageClass.GLOBAL)
				.map(occ -> (LeftHandSideOccurrence) occ);
	}

	public boolean assignsNonGlobalVariables() {
		return nonGlobalVariablesAssigned().findAny().isPresent();
	}

	private void process(final BoogieASTNode node) {
		switch (node) {
		case final ASTType type -> processType(type);
		case final Attribute attr -> processAttribute(attr);
		case final Body body -> processBody(body);
		case final Declaration decl -> processDeclaration(decl);
		case final Expression expr -> processExpression(expr);
		case final LeftHandSide lhs -> processLeftHandSide(lhs);
		case final Specification spec -> processSpecification(spec);
		case final Statement stmt -> processStatement(stmt);
		case final VarList vlist -> processVarList(vlist);

		// unsupported cases
		case final ParentEdge parent -> throw new UnsupportedOperationException();
		case final Project proj -> throw new UnsupportedOperationException();
		case final Unit unit -> throw new UnsupportedOperationException();
		case final BoogieASTNode n -> throw new UnsupportedOperationException();
		}
	}

	@Override
	protected void visit(final IdentifierExpression expr) {
		mResult.add(new IdentifierExpressionOccurrence(expr.getIdentifier(), expr.getDeclarationInformation(),
				mInOldContext));
	}

	@Override
	protected void visit(final VariableLHS lhs) {
		if (!mIgnoreLHS) {
			mResult.add(new LeftHandSideOccurrence(lhs.getIdentifier(), lhs.getDeclarationInformation()));
		}
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (!mIgnoreOldNonOldContext && expr instanceof final UnaryExpression unExpr
				&& unExpr.getOperator() == UnaryExpression.Operator.OLD) {
			final boolean prevContext = mInOldContext;
			mInOldContext = true;
			final var result = super.processExpression(expr);
			mInOldContext = prevContext;
			return result;
		}
		return super.processExpression(expr);
	}

	public static List<String> extractIds(final Expression expr) {
		return new BoogieVariableCollector(expr, true, false).collectedOccurences().stream()
				.map(occ -> occ.identifier()).distinct().toList();
	}

	public sealed interface VariableOccurrence {
		String identifier();

		DeclarationInformation declarationInformation();
	}

	public record IdentifierExpressionOccurrence(String identifier, DeclarationInformation declarationInformation,
			boolean inOldContext) implements VariableOccurrence {
	}

	public record LeftHandSideOccurrence(String identifier, DeclarationInformation declarationInformation)
			implements VariableOccurrence {
	}
}
