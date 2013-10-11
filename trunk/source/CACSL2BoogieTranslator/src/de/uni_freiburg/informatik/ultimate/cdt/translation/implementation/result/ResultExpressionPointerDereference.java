package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;


/**
 * Result for Pointer Dereference. The pointer is explicitly stored in 
 * m_Pointer.  
 * If the points to type is not a primitive type the expr may be null.
 * A typical application is not only *p, but also a field reference p->f,
 * where the m_Pointer has the appropriate offset 
 * @author Matthias Heizmann
 *
 */
public class ResultExpressionPointerDereference extends ResultExpression {
	
	public final Expression m_PointerBase;
	public final Expression m_PointerOffet;

	public ResultExpressionPointerDereference(ArrayList<Statement> stmt,
			Expression expr, ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars, 
			Expression pointerBase, Expression pointerOffset) {
		super(stmt, expr, decl, auxVars);
		m_PointerBase = pointerBase;
		m_PointerOffet = pointerOffset;
	}

}
