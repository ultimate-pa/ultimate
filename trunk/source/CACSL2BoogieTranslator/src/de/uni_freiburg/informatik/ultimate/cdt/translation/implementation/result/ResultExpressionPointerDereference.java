package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;


/**
 * Result for Pointer Dereference where the pointer is stored explicitly. The 
 * pointer can be given either as base and offset or directly by the expression 
 * m_Pointer.  
 * If the points-to-type is not a primitive type the expr may be null.
 * Otherwise expr is an auxiliary variables which is the result of a read call.
 * The declaration of this auxiliary variable and the read call are also stored.
 * This allows you to removed both if you do not want to dereference the pointer, 
 * e.g. because it occurs on the left hand side of an assignment. 
 * A typical application is not only *p, but also a field reference p->f,
 * where the m_Pointer has the appropriate offset 
 * @author Matthias Heizmann
 *
 */
public class ResultExpressionPointerDereference extends ResultExpression {
	
	public final Expression m_PointerBase;
	public final Expression m_PointerOffet;
	
	public final Expression m_Pointer;
	
	public final Statement m_ReadCall;
	public final VariableDeclaration m_CallResult;

	public ResultExpressionPointerDereference(ArrayList<Statement> stmt,
			Expression expr, ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars,
			Expression pointerBase, Expression pointerOffet,
			Statement readCall, VariableDeclaration callResult) {
		super(stmt, expr, decl, auxVars);
		m_PointerBase = pointerBase;
		m_PointerOffet = pointerOffet;
		m_ReadCall = readCall;
		m_CallResult = callResult;
		m_Pointer = null;
	}

	public ResultExpressionPointerDereference(ArrayList<Statement> stmt,
			Expression expr, ArrayList<Declaration> decl,
			Map<VariableDeclaration, CACSLLocation> auxVars,
			Expression pointer, Statement readCall,
			VariableDeclaration callResult) {
		super(stmt, expr, decl, auxVars);
		m_Pointer = pointer;
		m_ReadCall = readCall;
		m_CallResult = callResult;
		m_PointerBase = null;
		m_PointerOffet = null;
	}
	
	

}
