package de.uni_freiburg.informatik.ultimate.model.boogie;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;

/**
 * 
 * This class extends the original BoogieTransformer by providing simple visit
 * functions to all missing leaf types of BoogieTransformer.
 * 
 * It does NOT support transforming in those visit functions; if you want to do
 * this, you are better of with the original BoogieTransformer.
 * @param <RTR> Used to describe the return type of {@link #process(T)}.
 * @param <T> Used to describe the parameter type of {@link #process(T)}.
 * @author dietsch
 */
public abstract class BoogieVisitor extends BoogieTransformer {

	@Override
	protected Declaration processDeclaration(Declaration decl) {
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
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", decl.getClass()));
		}

		return super.processDeclaration(decl);
	}

	protected void visit(Axiom decl) {

	}

	protected void visit(ConstDeclaration decl) {

	}

	protected void visit(FunctionDeclaration decl) {

	}

	protected void visit(Procedure decl) {

	}

	protected void visit(TypeDeclaration decl) {

	}

	@Override
	protected ASTType processType(ASTType type) {
		if (type instanceof ArrayType) {
			visit((ArrayType) type);
		} else if (type instanceof NamedType) {
			visit((NamedType) type);
		} else if (type instanceof PrimitiveType) {
			visit((PrimitiveType) type);
		} else if (type instanceof StructType) {
			visit((StructType) type);
		} else {
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", type.getClass()));
		}
		return super.processType(type);
	}

	protected void visit(ArrayType type) {

	}

	protected void visit(NamedType type) {

	}

	protected void visit(PrimitiveType type) {

	}

	protected void visit(StructType type) {

	}

	@Override
	protected Statement processStatement(Statement statement) {
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
		} else {
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", statement.getClass()));
		}

		return super.processStatement(statement);
	}

	protected void visit(WhileStatement statement) {
	}

	protected void visit(ReturnStatement statement) {
	}

	protected void visit(Label statement) {
	}

	protected void visit(IfStatement statement) {
	}

	protected void visit(HavocStatement statement) {
	}

	protected void visit(GotoStatement statement) {
	}

	protected void visit(CallStatement statement) {
	}

	protected void visit(BreakStatement statement) {
	}

	protected void visit(AssignmentStatement statement) {

	}

	protected void visit(AssumeStatement statement) {

	}

	protected void visit(AssertStatement statement) {

	}

	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		if (lhs instanceof ArrayLHS) {
			visit((ArrayLHS) lhs);
		} else if (lhs instanceof StructLHS) {
			visit((StructLHS) lhs);
		} else if (lhs instanceof VariableLHS) {
			visit((VariableLHS) lhs);
		} else {
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", lhs.getClass()));
		}
		return super.processLeftHandSide(lhs);
	}

	protected void visit(VariableLHS lhs) {
	}

	protected void visit(StructLHS lhs) {
	}

	protected void visit(ArrayLHS lhs) {
	}

	@Override
	protected Specification processSpecification(Specification spec) {
		if (spec instanceof EnsuresSpecification) {
			visit((EnsuresSpecification) spec);
		} else if (spec instanceof LoopInvariantSpecification) {
			visit((LoopInvariantSpecification) spec);
		} else if (spec instanceof ModifiesSpecification) {
			visit((ModifiesSpecification) spec);
		} else if (spec instanceof RequiresSpecification) {
			visit((RequiresSpecification) spec);
		} else {
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", spec.getClass()));
		}
		return super.processSpecification(spec);
	}

	protected void visit(RequiresSpecification spec) {
	}

	protected void visit(ModifiesSpecification spec) {
	}

	protected void visit(LoopInvariantSpecification spec) {
	}

	protected void visit(EnsuresSpecification spec) {
	}

	@Override
	protected Attribute processAttribute(Attribute attr) {
		if (attr instanceof NamedAttribute) {
			visit((NamedAttribute) attr);
		} else if (attr instanceof Trigger) {
			visit((Trigger) attr);
		} else {
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", attr.getClass()));
		}

		return super.processAttribute(attr);
	}

	protected void visit(NamedAttribute attr) {

	}

	protected void visit(Trigger attr) {

	}

	@Override
	protected Expression processExpression(Expression expr) {
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
			throw new UnsupportedOperationException(String.format("Extend this with new type %s", expr.getClass()));
		}
		return super.processExpression(expr);
	}

	protected void visit(WildcardExpression expr) {
	}

	protected void visit(UnaryExpression expr) {
	}

	protected void visit(StructConstructor expr) {
	}

	protected void visit(StructAccessExpression expr) {
	}

	protected void visit(StringLiteral expr) {
	}

	protected void visit(RealLiteral expr) {
	}

	protected void visit(QuantifierExpression expr) {
	}

	protected void visit(IntegerLiteral expr) {
	}

	protected void visit(IfThenElseExpression expr) {
	}

	protected void visit(IdentifierExpression expr) {
	}

	protected void visit(FunctionApplication expr) {
	}

	protected void visit(BooleanLiteral expr) {
	}

	protected void visit(BitVectorAccessExpression expr) {
	}

	protected void visit(BitvecLiteral expr) {
	}

	protected void visit(BinaryExpression expr) {
	}

	protected void visit(ArrayStoreExpression expr) {
	}

	protected void visit(ArrayAccessExpression expr) {
	}

}
