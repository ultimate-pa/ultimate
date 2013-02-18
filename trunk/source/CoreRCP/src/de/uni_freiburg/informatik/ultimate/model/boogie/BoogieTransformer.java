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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WhileStatement;

/**
 * Base class to recursively walk through a Boogie tree, doing transformations.
 * This class changes nothing, but inherited classes may override some of 
 * the provided functions.  This class will then propagate the changes.
 *  
 * The boogie declaration is currently read-only, so all changes have to be returned
 * in new objects.  Therefore each of this function takes a Boogie-AST-node and 
 * returns the same type.  If the return value for the children do not change the 
 * default methods will return the same value again, so that no new objects are 
 * created.
 * 
 * As an example usage see de.uni_freiburg.informatik.ultimate.boogie.preprocessor.FunctionInliner.
 * Note that the underlying ITypes are not changed by the default implementation.  You
 * either need preserve types, run this before type checking, or take care of updating
 * the types yourself.
 * 
 * @author Jochen Hoenicke
 */
public abstract class BoogieTransformer {
	
	/**
	 * Process a declaration (including its children).
	 * @param decl the declaration to process.
	 * @return the processed declaration.
	 */
	protected Declaration processDeclaration(Declaration decl) {
		Attribute[] attrs = decl.getAttributes();
		Attribute[] newAttrs = processAttributes(attrs);
		if (decl instanceof TypeDeclaration) {
			TypeDeclaration tdecl = (TypeDeclaration) decl;
			ASTType syntype = tdecl.getSynonym();
			ASTType newSyntype = syntype != null ? processType(syntype) : null;
			if (newAttrs != attrs || newSyntype != syntype)
				return new TypeDeclaration(tdecl.getLocation(),
						newAttrs, tdecl.isFinite(), tdecl.getIdentifier(), tdecl.getTypeParams(), 
						newSyntype);
		} else if (decl instanceof ConstDeclaration) {
			ConstDeclaration cdecl = (ConstDeclaration) decl;
			VarList varList = cdecl.getVarList();
			VarList newVarList = processVarList(varList);
			if (newAttrs != attrs || newVarList != varList)
				return new ConstDeclaration(cdecl.getLocation(),
						newAttrs, cdecl.isUnique(), newVarList, cdecl.getParentInfo(), cdecl.isComplete());
		} else if (decl instanceof FunctionDeclaration) {
			FunctionDeclaration fdecl = (FunctionDeclaration) decl;
			VarList[] ins = fdecl.getInParams();
			VarList[] newIns = processVarLists(ins);
			VarList out = fdecl.getOutParam();
			VarList newOut = processVarList(out);
			Expression body = fdecl.getBody();
			Expression newBody = body != null ? processExpression(body) : null;
			if (newIns != ins || newOut != out
					|| newBody != body || newAttrs != attrs) {
				return  new FunctionDeclaration(fdecl.getLocation(), 
						newAttrs, fdecl.getIdentifier(), 
						fdecl.getTypeParams(), 
						newIns, newOut, newBody);
			}
		} else if (decl instanceof Axiom) {
			Expression ax = ((Axiom)decl).getFormula();
			Expression newAx = processExpression(ax);
			if (ax != newAx || attrs != newAttrs)
				return new Axiom(decl.getLocation(), newAttrs, newAx);
		} else if (decl instanceof Procedure) {
			Procedure proc = (Procedure) decl;
			VarList[] ins = proc.getInParams();
			VarList[] newIns = processVarLists(ins);
			VarList[] outs = proc.getOutParams();
			VarList[] newOuts = processVarLists(outs);
			Specification[] specs = proc.getSpecification();
			Specification[] newSpecs = specs != null ? processSpecifications(specs) : null;
			Body body = proc.getBody();
			Body newBody = body != null ? processBody(body) : null;
			if (newAttrs != attrs || newBody != body || newSpecs != specs
				|| newIns != ins || newOuts != outs)
				return new Procedure(proc.getLocation(),
						newAttrs, proc.getIdentifier(), 
						proc.getTypeParams(), 
						newIns, newOuts, 
						newSpecs, newBody);
		} else if (decl instanceof VariableDeclaration) {
			VarList[] vls = ((VariableDeclaration) decl).getVariables();
			VarList[] newVls = processVarLists(vls); 
			if (attrs != newAttrs || vls != newVls)
				return new VariableDeclaration(
						decl.getLocation(),
						newAttrs, newVls);
		}
		return decl;
	}

	/**
	 * Process an array of AST type.
	 * This implementation calls processType on all elements
	 * @param types the types to process.
	 * @return the processed types.
	 */
	protected ASTType[] processTypes(ASTType[] types) {
		boolean changed = false;
		ASTType[] newTypes = new ASTType[types.length];
		for (int i = 0; i < types.length; i++) {
			newTypes[i] = processType(types[i]);
			if (newTypes[i] != types[i])
				changed = true;
		}
		return changed ? newTypes : types;
	}

	/**
	 * Process a AST type.
	 * This implementation recurses on the sub types.
	 * @param type the type to process.
	 * @return the processed type.
	 */
	protected ASTType processType(ASTType type) {
		if (type instanceof ArrayType) {
			ArrayType arrtype = (ArrayType) type;
			ASTType[] indexTypes = arrtype.getIndexTypes();
			ASTType   valueType  = arrtype.getValueType();
			ASTType[] newIndexTypes = processTypes(indexTypes);
			ASTType   newValueType  = processType(valueType);
			if (newIndexTypes != indexTypes
				|| newValueType != valueType)
				return new ArrayType(arrtype.getLocation(), arrtype.getBoogieType(),
						arrtype.getTypeParams(), newIndexTypes, newValueType);
		} else if (type instanceof NamedType) {
			NamedType ntype = (NamedType) type;
			ASTType[] argTypes = ntype.getTypeArgs();
			ASTType[] newArgTypes = processTypes(argTypes);
			if (newArgTypes != argTypes)
				return new NamedType(ntype.getLocation(), ntype.getBoogieType(), ntype.getName(), newArgTypes);
		}
		return type;
	}

	/**
	 * Process an array of  variable list as it appears in function- and variable-specifications.
	 * This implementation calls processVarList on all elements.
	 * @param vls the variable lists
	 * @return the processed variable lists.
	 */
	protected VarList[] processVarLists(VarList[] vls) {
		boolean changed = false;
		VarList[] newVls = new VarList[vls.length];
		for (int i = 0; i < vls.length; i++) {
			newVls[i] = processVarList(vls[i]);
			if (newVls[i] != vls[i])
				changed = true;
		}
		return changed ? newVls : vls;
	}

	/**
	 * Process a variable list as it appears in function- and variable-specifications.
	 * This implementation processes the where clause and the type.
	 * @param vl the variable list
	 * @return the processed variable list.
	 */
	protected VarList processVarList(VarList vl) {
		ASTType type = vl.getType();
		ASTType newType = processType(type);
		Expression where = vl.getWhereClause();
		Expression newWhere = where != null ? processExpression(where) : null;
		if (newType != type || newWhere != where)
			return new VarList(vl.getLocation(), vl.getIdentifiers(), newType, newWhere); 
		return vl;
	}

	/**
	 * Process the body of an implementation.  Processes the contained variable declarations and
	 * statements.
	 * @param body the implementation body.
	 * @return the processed body.
	 */
	protected Body processBody(Body body) {
		VariableDeclaration[] locals = body.getLocalVars();
		VariableDeclaration[] newLocals = processLocalVariableDeclarations(locals);
		
		Statement[] statements = body.getBlock();
		Statement[] newStatements = processStatements(statements);
		if (newLocals != locals || newStatements != statements)
			return new Body(body.getLocation(), newLocals, newStatements);
		return body;
	}

	/**
	 * Process a local variable declaration.  Global declarations are processed by 
	 * processDeclaration.
	 * @param local The local variable declaration.
	 * @return the processed declaration.
	 */
	protected VariableDeclaration processLocalVariableDeclaration(VariableDeclaration local) {
		Attribute[] attrs = local.getAttributes();
		Attribute[] newAttrs = processAttributes(attrs);
		VarList[] vl = local.getVariables();
		VarList[] newVl = processVarLists(vl);
		if (vl != newVl || attrs != newAttrs) {
			return new VariableDeclaration(local.getLocation(),	newAttrs, newVl);
		}
		return local;
	}

	/**
	 * Process array of local variable declarations.  This is called for implementations.
	 * @param locals the array of variable declarations
	 * @return the processed declarations.
	 */
	protected VariableDeclaration[] processLocalVariableDeclarations(VariableDeclaration[] locals) {
		boolean changed = false;
		VariableDeclaration[] newLocals = new VariableDeclaration[locals.length];
		for (int i = 0; i < locals.length; i++) {
			newLocals[i] = processLocalVariableDeclaration(locals[i]);
			if (newLocals[i] != locals[i])
				changed = true;
		}
		return changed ? newLocals : locals;
	}

	/**
	 * Process the statements.  Calls processStatement for all statements in the array.
	 * @param statements the statement to process.
	 * @return processed statements.
	 */
	protected Statement[] processStatements(Statement[] statements) {
		boolean changed = false;
		Statement[] newStatements = new Statement[statements.length];
		for (int i = 0; i < statements.length; i++) {
			newStatements[i] = processStatement(statements[i]);
			if (newStatements[i] != statements[i])
				changed = true;
		}
		return changed ? newStatements : statements;
	}

	/**
	 * Process the statement.  Calls processExpression for all contained
	 * expressions and recurses for while and if statements.
	 * @param statement the statement to process.
	 * @return processed statement.
	 */
	protected Statement processStatement(Statement statement) {
		if (statement instanceof AssertStatement) {
			Expression expr = ((AssertStatement) statement).getFormula();
			Expression newExpr = processExpression(expr);
			if (expr != newExpr)
				return new AssertStatement(
						statement.getLocation(), newExpr);
		} else if (statement instanceof AssignmentStatement) {
			AssignmentStatement assign = (AssignmentStatement) statement;
			LeftHandSide[] lhs = assign.getLhs();
			LeftHandSide[] newLhs = processLeftHandSides(lhs);
			Expression[] rhs = assign.getRhs();
			Expression[] newRhs = processExpressions(rhs);
			if (lhs != newLhs || rhs != newRhs)
				return new AssignmentStatement(
						statement.getLocation(), 
						newLhs, newRhs);
		} else if (statement instanceof AssumeStatement) {
			Expression expr = ((AssumeStatement) statement).getFormula();
			Expression newExpr = processExpression(expr);
			if (expr != newExpr)
				return new AssumeStatement(
						statement.getLocation(), newExpr);
		} else if (statement instanceof CallStatement) {
			CallStatement call = (CallStatement) statement;
			Expression[] args = call.getArguments();
			Expression[] newArgs = processExpressions(args);
			if (args != newArgs)
				return new CallStatement(call.getLocation(), 
						call.isForall(),
						call.getLhs(), call.getMethodName(), newArgs);
		} else if (statement instanceof IfStatement) {
			IfStatement ifstmt = (IfStatement) statement;
			Expression cond = ifstmt.getCondition();
			Expression newCond = processExpression(cond);
			Statement[] thens = ifstmt.getThenPart();
			Statement[] newThens = processStatements(thens);
			Statement[] elses = ifstmt.getElsePart();
			Statement[] newElses = processStatements(elses);
			if (newCond != cond || newThens != thens || newElses != elses)
				return new IfStatement(ifstmt.getLocation(),
						newCond, newThens, newElses);
		} else if (statement instanceof WhileStatement) {
			WhileStatement whilestmt = (WhileStatement) statement;
			Expression cond = whilestmt.getCondition();
			Expression newCond = processExpression(cond);
			LoopInvariantSpecification[] invs = whilestmt.getInvariants();
			LoopInvariantSpecification[] newInvs = processLoopSpecifications(invs);
			Statement[] body = whilestmt.getBody();
			Statement[] newBody = processStatements(body);
			if (newCond != cond || newInvs != invs || newBody != body)
				return new WhileStatement(
						whilestmt.getLocation(),
						newCond, newInvs, newBody);
		}
		/* No recursion for label, havoc, break, return and goto */ 
		return statement;
	}

	/**
	 * Process the loop invariant specifications.  Calls processExpression for all
	 * loop invariants.
	 * @param specs the invariant specifications to process.
	 * @return processed specifications.
	 */
	protected LoopInvariantSpecification[] processLoopSpecifications(
			LoopInvariantSpecification[] specs) {
		boolean changed = false;
		LoopInvariantSpecification[] newSpecs = 
			new LoopInvariantSpecification[specs.length];
		for (int i = 0; i < newSpecs.length; i++) {
			Expression expr = ((LoopInvariantSpecification) specs[i]).getFormula();
			Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				changed = true;
				newSpecs[i] = new LoopInvariantSpecification(
						specs[i].getLocation(), 
						specs[i].isFree(), newExpr);
			} else
				newSpecs[i] = specs[i];
		}
		return changed ? newSpecs : specs;
	}

	/**
	 * Process a left hand side (of an assignement).  Recurses for array left hand side and
	 * calls processExpression for all contained expressions.
	 * @param lhs the left hand side to process.
	 * @return processed left hand side.
	 */
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			LeftHandSide array = alhs.getArray();
			LeftHandSide newArray = processLeftHandSide(array);
			Expression[] indices = alhs.getIndices();
			Expression[] newIndices = processExpressions(indices);
			if (array != newArray || indices != newIndices)
				return new ArrayLHS(lhs.getLocation(), alhs.getType(), newArray, newIndices);
		}
		return lhs;
	}
	
	/**
	 * Process the left hand sides (of an assignement).  Calls processLeftHandSide for
	 * each element in the array. 
	 * @param lhs the left hand sides to process.
	 * @return processed left hand sides.
	 */
	protected LeftHandSide[] processLeftHandSides(LeftHandSide[] lhs) {
		boolean changed = false;
		LeftHandSide[] newLhs = new LeftHandSide[lhs.length];
		for (int i = 0; i < newLhs.length; i++) {
			newLhs[i] = processLeftHandSide(lhs[i]);
			if (newLhs[i] != lhs[i])
				changed = true;
		}
		return changed ? newLhs : lhs;
	}

	/**
	 * Process a procedure specification.  Recursively calls processExpression
	 * for ensures and requires specifications.  This must not be called for
	 * LoopInvariantSpecifications.
	 * @param spec the specification to process.
	 * @return processed specification.
	 */
	protected Specification processSpecification(Specification spec) {
		if (spec instanceof EnsuresSpecification) {
			Expression expr = ((EnsuresSpecification) spec).getFormula();
			Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				return new EnsuresSpecification(
						spec.getLocation(), 
						spec.isFree(), newExpr);
			}
		} else if (spec instanceof RequiresSpecification) {
			Expression expr = ((RequiresSpecification) spec).getFormula();
			Expression newExpr = processExpression(expr);
			if (expr != newExpr) {
				return new RequiresSpecification(
						spec.getLocation(), 
						spec.isFree(), newExpr);
			}
		}
		return spec;
	}

	/**
	 * Process the procedure specifications.  Calls processSpecification for
	 * each element in the array. This must not be called for
	 * LoopInvariantSpecifications.
	 * @param specs the specifications to process.
	 * @return processed specifications.
	 */
	protected Specification[] processSpecifications(Specification[] specs) {
		boolean changed = false;
		Specification[] newSpecs = new Specification[specs.length];
		for (int i = 0; i < newSpecs.length; i++) {
			newSpecs[i] = processSpecification(specs[i]);
			if (newSpecs[i] != specs[i])
				changed = true;
		}
		return changed ? newSpecs : specs;
	}

	/**
	 * Process the attribute.  Calls processExpression for all contained expressions.
	 * This must handle all kinds of attributes, including triggers.
	 * @param attr the attribute to process.
	 * @return processed attribute.
	 */
	protected Attribute processAttribute(Attribute attr) {
		if (attr instanceof Trigger) {
			Expression[] exprs = ((Trigger)attr).getTriggers();
			Expression[] newExprs = processExpressions(exprs);
			if (newExprs != exprs)
				return new Trigger(attr.getLocation(), newExprs);
		} else if (attr instanceof NamedAttribute) {
			Expression[] exprs = ((NamedAttribute)attr).getValues();
			Expression[] newExprs = processExpressions(exprs);
			if (newExprs != exprs)
				return new NamedAttribute(attr.getLocation(),
						((NamedAttribute)attr).getName(), newExprs);
		}
		return attr;
	}
	
	/**
	 * Process the attributes.  Calls processAttribute for
	 * each element in the array. This must handle all kinds of attributes, including triggers.
	 * @param attributes the attributes to process.
	 * @return processed attributes.
	 */
	protected Attribute[] processAttributes(Attribute[] attributes) {
		boolean changed = false;
		Attribute[] newAttrs = new Attribute[attributes.length];
		for (int i = 0; i < attributes.length; i++) {
			newAttrs[i] = processAttribute(attributes[i]);
			if (newAttrs[i] != attributes[i])
				changed = true;
		}
		return changed ? newAttrs : attributes;
	}

	/**
	 * Process the expressions.  Calls processExpression for
	 * each element in the array. 
	 * @param exprs the expression to process.
	 * @return processed expressions.
	 */
	protected Expression[] processExpressions(Expression[] exprs) {
		Expression[] newExprs = new Expression[exprs.length];
		boolean changed = false;
		for (int j = 0; j < exprs.length; j++) {
			newExprs[j] = processExpression(exprs[j]);
			if (newExprs[j] != exprs[j])
				changed = true;
		}
		return changed ? newExprs : exprs;
	}

	/**
	 * Process the expressions.  Calls processExpression for
	 * each subexpression. 
	 * @param expr the expression to process.
	 * @return processed expression.
	 */
	protected Expression processExpression(Expression expr) {
		if (expr instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) expr;
			Expression left = processExpression(binexp.getLeft());
			Expression right = processExpression(binexp.getRight());
			if (left != binexp.getLeft()
				|| right != binexp.getRight()) {
				return new BinaryExpression(expr.getLocation(), binexp.getType(),
						binexp.getOperator(), left, right);
			}
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression unexp = (UnaryExpression) expr;
			Expression subexpr = processExpression(unexp.getExpr());
			if (subexpr != unexp.getExpr()) {
				return new UnaryExpression(expr.getLocation(), unexp.getType(),
						unexp.getOperator(), subexpr);
			}
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
			Expression arr = processExpression(aaexpr.getArray());
			boolean changed = arr != aaexpr.getArray();
			Expression[] indices = aaexpr.getIndices();
			Expression[] newIndices = new Expression[indices.length];
			for (int i = 0; i < indices.length; i++) {
				newIndices[i] = processExpression(indices[i]);
				if (newIndices[i] != indices[i])
					changed = true;
			}
			if (changed)
				return new ArrayAccessExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices);
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression aaexpr = (ArrayStoreExpression) expr;
			Expression arr = processExpression(aaexpr.getArray());
			Expression value = processExpression(aaexpr.getValue());
			boolean changed = arr != aaexpr.getArray() || value != aaexpr.getValue();
			Expression[] indices = aaexpr.getIndices();
			Expression[] newIndices = new Expression[indices.length];
			for (int i = 0; i < indices.length; i++) {
				newIndices[i] = processExpression(indices[i]);
				if (newIndices[i] != indices[i])
					changed = true;
			}
			if (changed)
				return new ArrayStoreExpression(aaexpr.getLocation(), aaexpr.getType(), arr, newIndices, value);
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression bvaexpr = 
				(BitVectorAccessExpression) expr;
			Expression bv = processExpression(bvaexpr.getBitvec());
			if (bv != bvaexpr.getBitvec())
				return new BitVectorAccessExpression(bvaexpr.getLocation(), bvaexpr.getType(), bv, 
						bvaexpr.getEnd(), bvaexpr.getStart());
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication app = (FunctionApplication) expr;
			String name = app.getIdentifier();
			Expression[] args = processExpressions(app.getArguments());
			if (args != app.getArguments())
				return new FunctionApplication(app.getLocation(),app.getType(), name, args);
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression ite = (IfThenElseExpression) expr;
			Expression cond = processExpression(ite.getCondition());
			Expression thenPart = processExpression(ite.getThenPart());
			Expression elsePart = processExpression(ite.getElsePart());
			if (cond != ite.getCondition()
			    || thenPart != ite.getThenPart()
			    || elsePart != ite.getElsePart())
				return new IfThenElseExpression(ite.getLocation(), ite.getType(), cond, thenPart, elsePart);
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quant = (QuantifierExpression) expr;
			Attribute[] attrs = quant.getAttributes();
			Attribute[] newAttrs = processAttributes(attrs);
			VarList[] params = quant.getParameters();
			VarList[] newParams = processVarLists(params);
			Expression subform = processExpression(quant.getSubformula());
			if (subform != quant.getSubformula()
				|| attrs != newAttrs
				|| params != newParams)
				return new QuantifierExpression(quant.getLocation(),quant.getType(), quant.isUniversal(), 
						quant.getTypeParams(), newParams, newAttrs, subform);
		}
		/* BooleanLiteral, IntegerLiteral, BitvecLiteral, StringLiteral, IdentifierExpression
		 * and WildcardExpression do not need recursion.
		 */ 
		return expr;
	}
}
