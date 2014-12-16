package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

// TODO map variables in attributes (?)
public class MappingExecutor {

	public static Specification mapVariables(Specification spec, IStringMapper mapper) {
		if (spec instanceof ModifiesSpecification) {
			ModifiesSpecification s = (ModifiesSpecification) spec;
			return new ModifiesSpecification(s.getLocation(), s.isFree(),
					mapVariables(s.getIdentifiers(), mapper));
		}
		if (spec instanceof RequiresSpecification) {
			RequiresSpecification s = (RequiresSpecification) spec;
			return new RequiresSpecification(s.getLocation(), s.isFree(),
					mapVariables(s.getFormula(), mapper));
		} 
		if (spec instanceof EnsuresSpecification) {
			EnsuresSpecification s = (EnsuresSpecification) spec;
			return new EnsuresSpecification(s.getLocation(), s.isFree(),
					mapVariables(s.getFormula(), mapper));
		}
		if (spec instanceof LoopInvariantSpecification) {
			LoopInvariantSpecification s = (LoopInvariantSpecification) spec;
			return new LoopInvariantSpecification(s.getLocation(), s.isFree(),
					mapVariables(s.getFormula(), mapper));
		}
		return spec; // assume the specification has nothing to rename
	}

	public static Specification[] mapVariables(Specification[] specs, IStringMapper mapper) {
		Specification[] mappedSpecs = new Specification[specs.length];
		for (int i = 0; i < specs.length; ++i) {
			mappedSpecs[i] = mapVariables(specs[i], mapper);
		}
		return mappedSpecs;
	}
	
	public static Expression mapVariables(Expression expr, IStringMapper mapper) {
		if (expr instanceof IdentifierExpression) { // trivial case
			IdentifierExpression e = (IdentifierExpression) expr;
			return new IdentifierExpression(e.getLocation(), e.getType(),
					mapper.map(e.getIdentifier()), e.getDeclarationInformation());
		}

		if (expr instanceof ArrayAccessExpression) {
			ArrayAccessExpression e = (ArrayAccessExpression) expr;
			return new ArrayAccessExpression(e.getLocation(), e.getType(),
					mapVariables(e.getArray(), mapper),
					mapVariables(e.getIndices(), mapper));
		}
		if (expr instanceof ArrayStoreExpression) {
			ArrayStoreExpression e = (ArrayStoreExpression) expr;
			return new ArrayStoreExpression(e.getLocation(), e.getType(),
					mapVariables(e.getArray(), mapper),
					mapVariables(e.getIndices(), mapper),
					mapVariables(e.getValue(), mapper));
		}
		if (expr instanceof BinaryExpression) {
			BinaryExpression e = (BinaryExpression) expr;
			return new BinaryExpression(e.getLocation(), e.getOperator(),
					mapVariables(e.getLeft(), mapper),
					mapVariables(e.getRight(), mapper));
		}
		if (expr instanceof BitVectorAccessExpression) {
			BitVectorAccessExpression e = (BitVectorAccessExpression) expr;
			return new BitVectorAccessExpression(e.getLocation(), e.getType(),
					mapVariables(e.getBitvec(), mapper), e.getEnd(), e.getStart());
		}
		if (expr instanceof FunctionApplication) {
			FunctionApplication e = (FunctionApplication) expr;
			// it would be possible to apply another mapper on "identifier" to refactor functions, too.
			return new FunctionApplication(e.getLocation(), e.getType(), e.getIdentifier(),
					mapVariables(e.getArguments(), mapper));
		}
		if (expr instanceof IfThenElseExpression) {
			IfThenElseExpression e = (IfThenElseExpression) expr;
			return new IfThenElseExpression(e.getLocation(), e.getType(),
					mapVariables(e.getCondition(), mapper),
					mapVariables(e.getThenPart(), mapper),
					mapVariables(e.getElsePart(), mapper));
		}
		if (expr instanceof QuantifierExpression) {
			QuantifierExpression e = (QuantifierExpression) expr;
			return new QuantifierExpression(e.getLocation(), e.getType(), e.isUniversal(), e.getTypeParams(),
					mapVariables(e.getParameters(), mapper),
					e.getAttributes(), // TODO map attributes? (do they have their own scope?) // TODO // TODO // TODO
					mapVariables(e.getSubformula(), mapper));
		}
		if (expr instanceof StructAccessExpression) {
			StructAccessExpression e = (StructAccessExpression) expr;
			return new StructAccessExpression(e.getLocation(), e.getType(),
					mapVariables(e.getStruct(), mapper), e.getField());
		}
		if (expr instanceof StructConstructor) {
			StructConstructor e = (StructConstructor) expr;
			return new StructConstructor(expr.getLocation(), e.getType(), e.getFieldIdentifiers(),
					mapVariables(e.getFieldValues(), mapper));
		}
		if (expr instanceof UnaryExpression) {
			UnaryExpression e = (UnaryExpression) expr;
			return new UnaryExpression(e.getLocation(), e.getType(), e.getOperator(),
					mapVariables(e.getExpr(), mapper));
		}
		// TODO support the following expression types (?)
		// if (expr instanceof TemporaryPointerExpression) {}
		// if (expr instanceof WildcardExpression) {}

		return expr; // assume that expression is a literal -- nothing to refactor
	}
	
	public static Expression[] mapVariables(Expression[] exprs, IStringMapper mapper) {
		Expression[] mappedExprs = new Expression[exprs.length];
		for (int i = 0; i < exprs.length; ++i) {
			mappedExprs[i] = mapVariables(exprs[i], mapper);
		}
		return mappedExprs;
	}
	
	public static VarList mapVariables(VarList varList, IStringMapper mapper) {
		return new VarList(varList.getLocation(),
				map(varList.getIdentifiers(), mapper), varList.getType(),
				mapVariables(varList.getWhereClause(), mapper));
	}
	
	public static VarList[] mapVariables(VarList[] varLists, IStringMapper mapper) {
		VarList[] mappedVarLists = new VarList[varLists.length];
		for (int i = 0; i < varLists.length; ++i) {
			mappedVarLists[i] = mapVariables(varLists[i], mapper);
		}
		return mappedVarLists;
	}
	

	public static VariableLHS mapVariables(VariableLHS var, IStringMapper mapper) {
		return new VariableLHS(var.getLocation(), var.getType(),
				mapper.map(var.getIdentifier()), var.getDeclarationInformation());
	}
	
	public static VariableLHS[] mapVariables(VariableLHS[] vars, IStringMapper mapper) {
		VariableLHS[] mappedVars = new VariableLHS[vars.length];
		for (int i = 0; i < vars.length; ++i) {
			mappedVars[i] = mapVariables(vars[i], mapper);
		}
		return mappedVars;
	}
	
	public static String[] map(String[] identifiers, IStringMapper mapper) {
		String[] mappedIdentifiers = new String[identifiers.length];
		for (int i = 0; i < identifiers.length; ++i) {
			mappedIdentifiers[i] = mapper.map(identifiers[i]);
		}
		return mappedIdentifiers;
	}
}
