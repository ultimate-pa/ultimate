package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class CompoundStatementExpressionResult extends ExpressionResult {

	public CompoundStatementExpressionResult(ArrayList<Statement> stmt, LRValue lrVal, ArrayList<Declaration> decl,
			Map<VariableDeclaration, ILocation> auxVars, List<Overapprox> overapproxList) {
		super(stmt, lrVal, decl, auxVars, overapproxList);
	}

//	public CompoundStatementExpressionResult(BoogieASTNode node) {
//		super(node);
//		stmt = null;
//		decl = null;
//		expr = null;
//	}
	
//	public CompoundStatementExpressionResult(List<Statement> s, List<Declaration> d, LRValue e) {
//		super(null);
//		stmt = s;
//		decl = d;
//		expr = e;
//	}
//	
//	public final List<Statement> stmt;
//	public final List<Declaration> decl;
//	public final LRValue expr;

}
