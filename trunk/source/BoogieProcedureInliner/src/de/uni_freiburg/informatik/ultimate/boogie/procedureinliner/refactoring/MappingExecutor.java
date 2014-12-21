package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring;

import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

// TODO map variables in attributes (?)

// This is somewhat similar to the BoogieTransformer (TODO consider to inherit).

/**
 * Unfinished -- do not use.
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class MappingExecutor {

	private final IStringMapper mMapper;
	
	public MappingExecutor(IStringMapper mapper) {
		mMapper = mapper;
	}
	
	public MappingExecutor(HashMap<String, String> mapping) {
		mMapper = new StringMapper(mapping);
	}

	public String[] map(String[] identifiers) {
		String[] mappedIdentifiers = new String[identifiers.length];
		for (int i = 0; i < identifiers.length; ++i) {
			mappedIdentifiers[i] = mMapper.map(identifiers[i]);
		}
		return mappedIdentifiers;
	}

	public Specification map(Specification spec) {
		if (spec instanceof ModifiesSpecification) {
			ModifiesSpecification s = (ModifiesSpecification) spec;
			return new ModifiesSpecification(s.getLocation(), s.isFree(), map(s.getIdentifiers()));
		}
		if (spec instanceof RequiresSpecification) {
			RequiresSpecification s = (RequiresSpecification) spec;
			return new RequiresSpecification(s.getLocation(), s.isFree(), map(s.getFormula()));
		} 
		if (spec instanceof EnsuresSpecification) {
			EnsuresSpecification s = (EnsuresSpecification) spec;
			return new EnsuresSpecification(s.getLocation(), s.isFree(), map(s.getFormula()));
		}
		if (spec instanceof LoopInvariantSpecification) {
			LoopInvariantSpecification s = (LoopInvariantSpecification) spec;
			return new LoopInvariantSpecification(s.getLocation(), s.isFree(), map(s.getFormula()));
		}
		return spec; // assume the specification has nothing to rename
	}

	public Specification[] map(Specification[] specs) {
		Specification[] mappedSpecs = new Specification[specs.length];
		for (int i = 0; i < specs.length; ++i) {
			mappedSpecs[i] = map(specs[i]);
		}
		return mappedSpecs;
	}
	
	LoopInvariantSpecification[] map(LoopInvariantSpecification[] specs) {
		LoopInvariantSpecification[] mappedSpecs = new LoopInvariantSpecification[specs.length];
		for (int i = 0; i < specs.length; ++i) {
			mappedSpecs[i] = (LoopInvariantSpecification) map(specs[i]);
		}
		return mappedSpecs;
	}
	
	public Expression map(Expression expr) {
		// trivial case ----
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression e = (IdentifierExpression) expr;
			return new IdentifierExpression(e.getLocation(), e.getType(), mMapper.map(e.getIdentifier()),
					e.getDeclarationInformation());
		}
		// non-trivial cases ----
		if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression e = (ArrayAccessExpression) expr;
			return new ArrayAccessExpression(e.getLocation(), e.getType(), map(e.getArray()), map(e.getIndices()));
		}
		if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression e = (ArrayStoreExpression) expr;
			return new ArrayStoreExpression(e.getLocation(), e.getType(), map(e.getArray()), map(e.getIndices()),
					map(e.getValue()));
		}
		if (expr instanceof BinaryExpression) {
			BinaryExpression e = (BinaryExpression) expr;
			return new BinaryExpression(e.getLocation(), e.getOperator(), map(e.getLeft()), map(e.getRight()));
		}
		if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression e = (BitVectorAccessExpression) expr;
			return new BitVectorAccessExpression(e.getLocation(), e.getType(), map(e.getBitvec()), e.getEnd(),
					e.getStart());
		}
		if (expr instanceof FunctionApplication) {
			FunctionApplication e = (FunctionApplication) expr;
			return new FunctionApplication(e.getLocation(), e.getType(), e.getIdentifier(), map(e.getArguments()));
		}
		if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression e = (IfThenElseExpression) expr;
			return new IfThenElseExpression(e.getLocation(), e.getType(), map(e.getCondition()), map(e.getThenPart()),
					map(e.getElsePart()));
		}
		if (expr instanceof QuantifierExpression) {
			throw new UnsupportedOperationException("Quantifiers aren't supported yet.");
			// TODO support
			/*
			QuantifierExpression e = (QuantifierExpression) expr;
			return new QuantifierExpression(e.getLocation(), e.getType(), e.isUniversal(), e.getTypeParams(),
					e.getParameters(), // TODO rename, avoiding name collisions -----------------+
					e.getAttributes(), // map attributes? (do they have their own scope?)        |
					map(e.getSubformula())); // Rename bound variables, too <---+
					
			*/
		}
		if (expr instanceof StructAccessExpression) {
			StructAccessExpression e = (StructAccessExpression) expr;
			return new StructAccessExpression(e.getLocation(), e.getType(), map(e.getStruct()), e.getField());
		}
		if (expr instanceof StructConstructor) {
			StructConstructor e = (StructConstructor) expr;
			return new StructConstructor(expr.getLocation(), e.getType(), e.getFieldIdentifiers(),
					map(e.getFieldValues()));
		}
		if (expr instanceof UnaryExpression) {
			UnaryExpression e = (UnaryExpression) expr;
			return new UnaryExpression(e.getLocation(), e.getType(), e.getOperator(), map(e.getExpr()));
		}
		if (expr instanceof WildcardExpression) {
			throw new UnsupportedOperationException("WildcardExpressions aren't supported yet.");
		}
		// TemporaryPointerExpression is private (should never occur)

		return expr; // assume that expression is a literal => nothing to refactor
	}
	
	public Expression[] map(Expression[] exprs) {
		Expression[] mappedExprs = new Expression[exprs.length];
		for (int i = 0; i < exprs.length; ++i) {
			mappedExprs[i] = map(exprs[i]);
		}
		return mappedExprs;
	}
	
	public VarList map(VarList varList) {
		if (varList.getWhereClause() != null)
			throw new UnsupportedOperationException("Where clauses aren't supported yet.");
		return new VarList(varList.getLocation(),
				map(varList.getIdentifiers()), varList.getType(), /*WhereClause*/ null);
	}
	
	public VarList[] map(VarList[] varLists) {
		VarList[] mappedVarLists = new VarList[varLists.length];
		for (int i = 0; i < varLists.length; ++i) {
			mappedVarLists[i] = map(varLists[i]);
		}
		return mappedVarLists;
	}

	public VariableLHS map(VariableLHS var) {
		return new VariableLHS(var.getLocation(), var.getType(), mMapper.map(var.getIdentifier()),
				var.getDeclarationInformation());
	}
	
	public VariableLHS[] map(VariableLHS[] vars) {
		VariableLHS[] mappedVars = new VariableLHS[vars.length];
		for (int i = 0; i < vars.length; ++i) {
			mappedVars[i] = map(vars[i]);
		}
		return mappedVars;
	}

	// //////////////////////////////////////////////////////////
	
	public Declaration map(Procedure p) {
		if (p.getAttributes().length > 0)
			throw new UnsupportedOperationException("Attributes aren't supported yet.");
		Body body = p.getBody();
		Body newBody = null;
		if (body != null)
			newBody = new Body(body.getLocation(), map(body.getLocalVars()), map(body.getBlock()));
		return new Procedure(p.getLocation(), p.getAttributes(), p.getIdentifier(), p.getTypeParams(),
				map(p.getInParams()), map(p.getOutParams()), map(p.getSpecification()), newBody);
	}

	private VariableDeclaration map(VariableDeclaration varDecl) {
		if (varDecl.getAttributes().length > 0)
			throw new UnsupportedOperationException("Attributes aren't supported yet.");
		return new VariableDeclaration(varDecl.getLocation(), varDecl.getAttributes(), map(varDecl.getVariables()));
	}
	
	private VariableDeclaration[] map(VariableDeclaration[] varDecls) {
		VariableDeclaration[] newVarDecls = new VariableDeclaration[varDecls.length];
		for (int i = 0; i < varDecls.length; ++i) {
			newVarDecls[i] = map(varDecls[i]);
		}
		return newVarDecls;
	}
	
	private Statement map(Statement stat) {
		if (stat instanceof AssertStatement) {
			AssertStatement s = (AssertStatement) stat;
			return new AssertStatement(s.getLocation(), map(s.getFormula()));
		}
		if (stat instanceof AssignmentStatement) {
			AssignmentStatement s = (AssignmentStatement) stat;
			return new AssignmentStatement(s.getLocation(), map(s.getLhs()), map(s.getRhs()));
		}
		if (stat instanceof AssumeStatement) {
			AssumeStatement s = (AssumeStatement) stat;
			return new AssumeStatement(s.getLocation(), map(s.getFormula()));
		}
		if (stat instanceof CallStatement) {
			CallStatement s = (CallStatement) stat;
			return new CallStatement(s.getLocation(), s.isForall(), map(s.getLhs()), s.getMethodName(),
					map(s.getArguments()));
		}
		if (stat instanceof HavocStatement) {
			HavocStatement s = (HavocStatement) stat;
			return new HavocStatement(s.getLocation(), map(s.getIdentifiers()));
		}
		if (stat instanceof IfStatement) {
			IfStatement s = (IfStatement) stat;
			return new IfStatement(s.getLocation(), map(s.getCondition()), map(s.getThenPart()), map(s.getElsePart()));
		}
		if (stat instanceof WhileStatement) {
			WhileStatement s = (WhileStatement) stat;
			return new WhileStatement(s.getLocation(), map(s.getCondition()), map(s.getInvariants()), map(s.getBody()));
		}
		// nothing to do for: BreakStatement, GotoStatement, Label, ReturnStatement
		return stat;
	}

	private LeftHandSide map(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return map((VariableLHS) lhs);
		}
		if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			return new ArrayLHS(alhs.getLocation(), alhs.getType(), map(alhs.getArray()), map(alhs.getIndices()));
		}
		if (lhs instanceof StructLHS) {
			StructLHS slhs = (StructLHS) lhs;
			return new StructLHS(slhs.getLocation(), slhs.getType(), map(slhs.getStruct()), slhs.getField());
		}
		throw new UnsupportedOperationException("Cannot process unknown LHS: " + lhs.getClass().getName());
	}
	
	private LeftHandSide[] map(LeftHandSide[] lhs) {
		LeftHandSide[] newLhs = new LeftHandSide[lhs.length];
		for (int i = 0; i < lhs.length; ++i) {
			newLhs[i] = map(lhs[i]);
		}
		return newLhs;
	}

	private Statement[] map(Statement[] statements) {
		Statement[] newStatements = new Statement[statements.length];
		for (int i = 0; i < statements.length; ++i) {
			newStatements[i] = map(statements[i]);
		}
		return newStatements;
	}

}
















