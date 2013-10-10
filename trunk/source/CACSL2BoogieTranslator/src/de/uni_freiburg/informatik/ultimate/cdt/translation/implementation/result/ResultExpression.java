/**
 * Describing a translation result for expressions.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 01.02.2012
 */
public class ResultExpression extends Result {
	/**
	 * Statement list.
	 */
	public final ArrayList<Statement> stmt;
	/**
	 * The expression.
	 */
	public Expression expr;
	/**
	 * Declaration list. Some translations need to declare some temporary
	 * variables, which we do here.
	 */
	public final ArrayList<Declaration> decl;
	/**
	 * A description of the C variable.
	 */
	public final ArrayList<CType> declCTypes;
	/**
	 * The description of the C type of this expression.
	 */
	public CType cType;
	
	/**
	 * Auxiliary variables occurring in this result. The variable declaration
	 * of the var is mapped to the exact location for that it was constructed.
	 */
	public final Map<VariableDeclaration, CACSLLocation> auxVars;

	/**
	 * Constructor.
	 * 
	 * @param stmt
	 *            the statement list to hold
	 * @param expr
	 *            the expression list to hold
	 * @param decl
	 *            the declaration list to hold
	 */
	public ResultExpression(ArrayList<Statement> stmt, Expression expr,
			ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars) {
		super(null);
		this.stmt = stmt;
		this.expr = expr;
		this.decl = decl;
		this.declCTypes = new ArrayList<CType>();
		this.auxVars = auxVars;
	}

	/**
	 * Constructor for only one element
	 * 
	 * @param expr
	 *            the expression to add
	 */
	public ResultExpression(Expression expr,
			Map<VariableDeclaration, CACSLLocation> auxVars) {
		super(null);
		this.stmt = new ArrayList<Statement>();
		this.expr = expr;
		this.decl = new ArrayList<Declaration>();
		this.declCTypes = new ArrayList<CType>();
		this.auxVars = auxVars;
	}
}
