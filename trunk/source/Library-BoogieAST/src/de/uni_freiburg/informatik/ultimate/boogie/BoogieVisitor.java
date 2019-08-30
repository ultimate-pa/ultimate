/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Lars Nitkze (lars.nitzke@mailfence.com)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;

/**
 *
 * This class extends the original BoogieTransformer by providing simple visit functions to all missing leaf types of
 * BoogieTransformer.
 *
 * It does NOT support transforming in those visit functions; if you want to do this, you are better of with the
 * original BoogieTransformer.
 *
 * @param <RTR>
 *            Used to describe the return type of {@link #process(T)}.
 * @param <T>
 *            Used to describe the parameter type of {@link #process(T)}.
 * @author dietsch
 */
public abstract class BoogieVisitor extends BoogieTransformer {

	private static final String MSG_EXTEND_THIS_WITH_NEW_TYPE = "Extend this with new type %s";

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		if (decl instanceof Axiom) {
			visit((Axiom) decl);
		} else if (decl instanceof ConstDeclaration) {
			visit((ConstDeclaration) decl);
		} else if (decl instanceof FunctionDeclaration) {
			visit((FunctionDeclaration) decl);
		} else if (decl instanceof Procedure) {
			visit((Procedure) decl);
		} else if (decl instanceof TypeDeclaration) {
			visit((TypeDeclaration) decl);
		} else if (decl instanceof VariableDeclaration) {
			// this case is already handled by processVariableDeclaration
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, decl.getClass()));
		}

		return super.processDeclaration(decl);
	}

	protected void visit(final Axiom decl) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ConstDeclaration decl) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final FunctionDeclaration decl) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final Procedure decl) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final TypeDeclaration decl) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected ASTType processType(final ASTType type) {
		if (type instanceof ArrayType) {
			visit((ArrayType) type);
		} else if (type instanceof NamedType) {
			visit((NamedType) type);
		} else if (type instanceof PrimitiveType) {
			visit((PrimitiveType) type);
		} else if (type instanceof StructType) {
			visit((StructType) type);
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, type.getClass()));
		}
		return super.processType(type);
	}

	protected void visit(final ArrayType type) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final NamedType type) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final PrimitiveType type) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructType type) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		if (statement instanceof AssertStatement) {
			visit((AssertStatement) statement);
		} else if (statement instanceof AssignmentStatement) {
			visit((AssignmentStatement) statement);
		} else if (statement instanceof AssumeStatement) {
			visit((AssumeStatement) statement);
		} else if (statement instanceof BreakStatement) {
			visit((BreakStatement) statement);
		} else if (statement instanceof CallStatement) {
			visit((CallStatement) statement);
		} else if (statement instanceof ForkStatement) {
			visit((ForkStatement) statement);
		} else if (statement instanceof JoinStatement) {
			visit((JoinStatement) statement);
		} else if (statement instanceof GotoStatement) {
			visit((GotoStatement) statement);
		} else if (statement instanceof HavocStatement) {
			visit((HavocStatement) statement);
		} else if (statement instanceof IfStatement) {
			visit((IfStatement) statement);
		} else if (statement instanceof Label) {
			visit((Label) statement);
		} else if (statement instanceof ReturnStatement) {
			visit((ReturnStatement) statement);
		} else if (statement instanceof WhileStatement) {
			visit((WhileStatement) statement);
		} else if (statement instanceof AtomicStatement) {
			visit((AtomicStatement) statement);
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, statement.getClass()));
		}

		return super.processStatement(statement);
	}

	protected void visit(final WhileStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AtomicStatement statment) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ReturnStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final Label statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IfStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final HavocStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final GotoStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final CallStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ForkStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final JoinStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BreakStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AssignmentStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AssumeStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AssertStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		if (lhs instanceof ArrayLHS) {
			visit((ArrayLHS) lhs);
		} else if (lhs instanceof StructLHS) {
			visit((StructLHS) lhs);
		} else if (lhs instanceof VariableLHS) {
			visit((VariableLHS) lhs);
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, lhs.getClass()));
		}
		return super.processLeftHandSide(lhs);
	}

	protected void visit(final VariableLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ArrayLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected Specification processSpecification(final Specification spec) {
		if (spec instanceof EnsuresSpecification) {
			visit((EnsuresSpecification) spec);
		} else if (spec instanceof LoopInvariantSpecification) {
			visit((LoopInvariantSpecification) spec);
		} else if (spec instanceof ModifiesSpecification) {
			visit((ModifiesSpecification) spec);
		} else if (spec instanceof RequiresSpecification) {
			visit((RequiresSpecification) spec);
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, spec.getClass()));
		}
		return super.processSpecification(spec);
	}

	protected void visit(final RequiresSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ModifiesSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final LoopInvariantSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final EnsuresSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected <T extends Attribute> T processAttribute(final T attr) {
		if (attr instanceof NamedAttribute) {
			visit((NamedAttribute) attr);
		} else if (attr instanceof Trigger) {
			visit((Trigger) attr);
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, attr.getClass()));
		}

		return super.processAttribute(attr);
	}

	protected void visit(final NamedAttribute attr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final Trigger attr) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		if (expr instanceof ArrayAccessExpression) {
			visit((ArrayAccessExpression) expr);
		} else if (expr instanceof ArrayStoreExpression) {
			visit((ArrayStoreExpression) expr);
		} else if (expr instanceof BinaryExpression) {
			visit((BinaryExpression) expr);
		} else if (expr instanceof BitvecLiteral) {
			visit((BitvecLiteral) expr);
		} else if (expr instanceof BitVectorAccessExpression) {
			visit((BitVectorAccessExpression) expr);
		} else if (expr instanceof BooleanLiteral) {
			visit((BooleanLiteral) expr);
		} else if (expr instanceof FunctionApplication) {
			visit((FunctionApplication) expr);
		} else if (expr instanceof IdentifierExpression) {
			visit((IdentifierExpression) expr);
		} else if (expr instanceof IfThenElseExpression) {
			visit((IfThenElseExpression) expr);
		} else if (expr instanceof IntegerLiteral) {
			visit((IntegerLiteral) expr);
		} else if (expr instanceof QuantifierExpression) {
			visit((QuantifierExpression) expr);
		} else if (expr instanceof RealLiteral) {
			visit((RealLiteral) expr);
		} else if (expr instanceof StringLiteral) {
			visit((StringLiteral) expr);
		} else if (expr instanceof StructAccessExpression) {
			visit((StructAccessExpression) expr);
		} else if (expr instanceof StructConstructor) {
			visit((StructConstructor) expr);
		} else if (expr instanceof UnaryExpression) {
			visit((UnaryExpression) expr);
		} else if (expr instanceof WildcardExpression) {
			visit((WildcardExpression) expr);
		} else {
			throw new UnsupportedOperationException(String.format(MSG_EXTEND_THIS_WITH_NEW_TYPE, expr.getClass()));
		}
		return super.processExpression(expr);
	}

	protected void visit(final WildcardExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final UnaryExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructConstructor expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructAccessExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StringLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final RealLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final QuantifierExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IntegerLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IfThenElseExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IdentifierExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final FunctionApplication expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BooleanLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BitVectorAccessExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BitvecLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BinaryExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ArrayStoreExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ArrayAccessExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

}
