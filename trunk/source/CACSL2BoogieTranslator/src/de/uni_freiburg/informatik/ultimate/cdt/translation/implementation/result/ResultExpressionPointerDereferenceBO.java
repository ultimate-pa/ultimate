//package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;
//
//import java.util.ArrayList;
//import java.util.Map;
//
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
//import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
//
//
///**
// * Special case of ResultExpressionPointerDereference where pointer is given
// * by m_PointerBase and m_PointerOffset. Here the pointer is an auxiliary
// * pointer declared by m_AuxPointer and defined by the two assume statements
// * m_BaseEquality and m_OffsetEquality.
// * 
// *
// */
//public class ResultExpressionPointerDereferenceBO extends ResultExpressionPointerDereference {
//
//	public final Expression m_PointerBase;
//	public final Expression m_PointerOffset;
//	public final VariableDeclaration m_AuxPointer;
//	public final AssumeStatement m_BaseEquality;
//	public final AssumeStatement m_OffsetEquality;
//	public ResultExpressionPointerDereferenceBO(ArrayList<Statement> stmt,
//			Expression expr, ArrayList<Declaration> decl,
//			Map<VariableDeclaration, CACSLLocation> auxVars,
//			Expression auxPointer,
//			Statement readCall, VariableDeclaration callResult, 
//			VariableDeclaration auxPointerDecl,
//			Expression pointerBase, Expression pointerOffset,
//			AssumeStatement baseEquality, AssumeStatement offsetEquality) {
//		super(stmt, expr, decl, auxVars, auxPointer, readCall, callResult);
//		m_PointerBase = pointerBase;
//		m_PointerOffset = pointerOffset;
//		m_AuxPointer = auxPointerDecl;
//		m_BaseEquality = baseEquality;
//		m_OffsetEquality = offsetEquality;
//	}
//	@Override
//	public void removePointerDereference() {
//		super.removePointerDereference();
//		boolean removed;
//		removed = stmt.remove(m_BaseEquality);
//		assert removed;
//		removed = stmt.remove(m_OffsetEquality);
//		assert removed;
//		removed = decl.remove(m_AuxPointer);
//		assert removed;
//		CACSLLocation value = auxVars.remove(m_AuxPointer);
//		assert value != null;
//	}
//	
//	
//	
//}
