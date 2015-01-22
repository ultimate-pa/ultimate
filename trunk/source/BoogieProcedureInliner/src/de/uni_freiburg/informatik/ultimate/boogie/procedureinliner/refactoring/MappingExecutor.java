package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring;

import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
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
		Specification newSpec = null;
		if (spec instanceof ModifiesSpecification) {
			ModifiesSpecification s = (ModifiesSpecification) spec;
			newSpec = new ModifiesSpecification(s.getLocation(), s.isFree(), map(s.getIdentifiers()));
		} else if (spec instanceof RequiresSpecification) {
			RequiresSpecification s = (RequiresSpecification) spec;
			newSpec = new RequiresSpecification(s.getLocation(), s.isFree(), map(s.getFormula()));
		} else if (spec instanceof EnsuresSpecification) {
			EnsuresSpecification s = (EnsuresSpecification) spec;
			newSpec = new EnsuresSpecification(s.getLocation(), s.isFree(), map(s.getFormula()));
		} else if (spec instanceof LoopInvariantSpecification) {
			LoopInvariantSpecification s = (LoopInvariantSpecification) spec;
			newSpec = new LoopInvariantSpecification(s.getLocation(), s.isFree(), map(s.getFormula()));
		}
		if (newSpec == null) {
			return spec; // assume the specification has nothing to rename			
		} else {
			ModelUtils.mergeAnnotations(spec, newSpec);
			return newSpec;
		}
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
		Expression newExpr = null;
		if (expr instanceof IdentifierExpression) { // trivial case
			IdentifierExpression e = (IdentifierExpression) expr;
			newExpr =  new IdentifierExpression(e.getLocation(), e.getType(), mMapper.map(e.getIdentifier()),
					e.getDeclarationInformation());
		} else if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression e = (ArrayAccessExpression) expr;
			newExpr = new ArrayAccessExpression(e.getLocation(), e.getType(), map(e.getArray()), map(e.getIndices()));
		} else if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression e = (ArrayStoreExpression) expr;
			newExpr = new ArrayStoreExpression(e.getLocation(), e.getType(), map(e.getArray()), map(e.getIndices()),
					map(e.getValue()));
		} else if (expr instanceof BinaryExpression) {
			BinaryExpression e = (BinaryExpression) expr;
			newExpr = new BinaryExpression(e.getLocation(), e.getOperator(), map(e.getLeft()), map(e.getRight()));
		} else if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression e = (BitVectorAccessExpression) expr;
			newExpr = new BitVectorAccessExpression(e.getLocation(), e.getType(), map(e.getBitvec()), e.getEnd(),
					e.getStart());
		} else if (expr instanceof FunctionApplication) {
			FunctionApplication e = (FunctionApplication) expr;
			newExpr = new FunctionApplication(e.getLocation(), e.getType(), e.getIdentifier(), map(e.getArguments()));
		} else if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression e = (IfThenElseExpression) expr;
			newExpr = new IfThenElseExpression(e.getLocation(), e.getType(), map(e.getCondition()), map(e.getThenPart()),
					map(e.getElsePart()));
		} else if (expr instanceof QuantifierExpression) {
			throw new UnsupportedOperationException("Quantifiers aren't supported yet.");
			// TODO support
			/*
			QuantifierExpression e = (QuantifierExpression) expr;
			return new QuantifierExpression(e.getLocation(), e.getType(), e.isUniversal(), e.getTypeParams(),
					e.getParameters(), // TODO rename, avoiding name collisions -----------------+
					e.getAttributes(), // map attributes? (do they have their own scope?)        |
					map(e.getSubformula())); // Rename bound variables, too <---+
					
			*/
		} else if (expr instanceof StructAccessExpression) {
			StructAccessExpression e = (StructAccessExpression) expr;
			newExpr = new StructAccessExpression(e.getLocation(), e.getType(), map(e.getStruct()), e.getField());
		} else if (expr instanceof StructConstructor) {
			StructConstructor e = (StructConstructor) expr;
			newExpr = new StructConstructor(expr.getLocation(), e.getType(), e.getFieldIdentifiers(),
					map(e.getFieldValues()));
		} else if (expr instanceof UnaryExpression) {
			UnaryExpression e = (UnaryExpression) expr;
			if (e.getOperator() == UnaryExpression.Operator.OLD)
				throw new UnsupportedOperationException("old(...) isn't supported yet.");
			return new UnaryExpression(e.getLocation(), e.getType(), e.getOperator(), map(e.getExpr()));
		}
		// TemporaryPointerExpression is private (should never occur)

		if (newExpr == null) {
			return expr; // assume that expression is a literal => nothing to refactor			
		} else {
			ModelUtils.mergeAnnotations(expr, newExpr);
			return newExpr;
		}
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
		VarList newVarList = new VarList(varList.getLocation(),
				map(varList.getIdentifiers()), varList.getType(), /*WhereClause*/ null);
		ModelUtils.mergeAnnotations(varList, newVarList);
		return newVarList;
	}
	
	public VarList[] map(VarList[] varLists) {
		VarList[] mappedVarLists = new VarList[varLists.length];
		for (int i = 0; i < varLists.length; ++i) {
			mappedVarLists[i] = map(varLists[i]);
		}
		return mappedVarLists;
	}

	public VariableLHS map(VariableLHS var) {
		VariableLHS newVar = new VariableLHS(var.getLocation(), var.getType(),
				mMapper.map(var.getIdentifier()), var.getDeclarationInformation());
		ModelUtils.mergeAnnotations(var, newVar);
		return newVar;
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
		Procedure newProc = new Procedure(p.getLocation(), p.getAttributes(), p.getIdentifier(), p.getTypeParams(),
				map(p.getInParams()), map(p.getOutParams()), map(p.getSpecification()), newBody);
		ModelUtils.mergeAnnotations(p, newProc);
		return newProc;
	}

	private VariableDeclaration map(VariableDeclaration varDecl) {
		if (varDecl.getAttributes().length > 0)
			throw new UnsupportedOperationException("Attributes aren't supported yet.");
		VariableDeclaration newVarDecl = new VariableDeclaration(varDecl.getLocation(),
				varDecl.getAttributes(), map(varDecl.getVariables()));
		ModelUtils.mergeAnnotations(varDecl, newVarDecl);
		return newVarDecl;
	}
	
	private VariableDeclaration[] map(VariableDeclaration[] varDecls) {
		VariableDeclaration[] newVarDecls = new VariableDeclaration[varDecls.length];
		for (int i = 0; i < varDecls.length; ++i) {
			newVarDecls[i] = map(varDecls[i]);
		}
		return newVarDecls;
	}
	
	private Statement map(Statement stat) {
		Statement newStat = null;
		if (stat instanceof AssertStatement) {
			AssertStatement s = (AssertStatement) stat;
			newStat = new AssertStatement(s.getLocation(), map(s.getFormula()));
		} else if (stat instanceof AssignmentStatement) {
			AssignmentStatement s = (AssignmentStatement) stat;
			newStat = new AssignmentStatement(s.getLocation(), map(s.getLhs()), map(s.getRhs()));
		} else if (stat instanceof AssumeStatement) {
			AssumeStatement s = (AssumeStatement) stat;
			newStat = new AssumeStatement(s.getLocation(), map(s.getFormula()));
		} else if (stat instanceof CallStatement) {
			CallStatement s = (CallStatement) stat;
			newStat = new CallStatement(s.getLocation(), s.isForall(), map(s.getLhs()), s.getMethodName(),
					map(s.getArguments()));
		} else if (stat instanceof HavocStatement) {
			HavocStatement s = (HavocStatement) stat;
			newStat = new HavocStatement(s.getLocation(), map(s.getIdentifiers()));
		} else if (stat instanceof IfStatement) {
			IfStatement s = (IfStatement) stat;
			newStat = new IfStatement(s.getLocation(), map(s.getCondition()), map(s.getThenPart()), map(s.getElsePart()));
		} else if (stat instanceof WhileStatement) {
			WhileStatement s = (WhileStatement) stat;
			newStat = new WhileStatement(s.getLocation(), map(s.getCondition()), map(s.getInvariants()), map(s.getBody()));
		}
		if (newStat == null) {
			return stat;// nothing to do for: BreakStatement, GotoStatement, Label, ReturnStatement
		} else {
			ModelUtils.mergeAnnotations(stat, newStat);
			return newStat;
		}
	}

	private LeftHandSide map(LeftHandSide lhs) {
		LeftHandSide newLhs = null;
		if (lhs instanceof VariableLHS) {
			newLhs = map((VariableLHS) lhs);
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			newLhs = new ArrayLHS(alhs.getLocation(), alhs.getType(), map(alhs.getArray()), map(alhs.getIndices()));
		} else if (lhs instanceof StructLHS) {
			StructLHS slhs = (StructLHS) lhs;
			newLhs = new StructLHS(slhs.getLocation(), slhs.getType(), map(slhs.getStruct()), slhs.getField());
		}
		if (newLhs == null) {
			throw new UnsupportedOperationException("Cannot process unknown LHS: " + lhs.getClass().getName());			
		} else {
			ModelUtils.mergeAnnotations(lhs, newLhs);
			return newLhs;
		}
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
















