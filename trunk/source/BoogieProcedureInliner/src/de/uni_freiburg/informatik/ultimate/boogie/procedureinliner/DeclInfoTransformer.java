package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Changes any other DeclarationInformation than GLOBAL and QUANTIFIED to be LOCAL.
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class DeclInfoTransformer extends BoogieTransformer {

	private String mProcName;
	
	/**
	 * Create a new transformer.
	 * @param procName Name of the procedure which contains all LHS as local variables
	 *                 (except for GLOBAL and QUANTIFIED).
	 */
	public DeclInfoTransformer(String procName) {
		mProcName = procName;
	}
	
	@Override
	public Statement processStatement(Statement statement) {
		return super.processStatement(statement);
	};
	
	@Override
	public Expression processExpression(Expression expr) {
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression ie = (IdentifierExpression) expr;
			DeclarationInformation newDeclInfo = processDeclInfo(ie.getDeclarationInformation());
			return new IdentifierExpression(ie.getLocation(), ie.getType(), ie.getIdentifier(), newDeclInfo);				
		} else {
			return super.processExpression(expr);			
		}
	}
	
	@Override
	public LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			VariableLHS vlhs = (VariableLHS) lhs;
			DeclarationInformation newDeclInfo = vlhs.getDeclarationInformation();
			if (newDeclInfo != null)
				newDeclInfo = processDeclInfo(newDeclInfo);
			return new VariableLHS(vlhs.getLocation(), vlhs.getType(), vlhs.getIdentifier(), newDeclInfo);
		} else if (lhs instanceof StructLHS) {
			StructLHS slhs = (StructLHS) lhs;
			LeftHandSide newStruct = processLeftHandSide(slhs.getStruct());
			return new StructLHS(slhs.getLocation(), slhs.getType(), newStruct, slhs.getField());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS alhs = (ArrayLHS) lhs;
			LeftHandSide newArray = processLeftHandSide(alhs.getArray());
			return new ArrayLHS(alhs.getLocation(), alhs.getType(), newArray, alhs.getIndices());
		} else {
			throw new UnsupportedOperationException("Unknown LHS: " + lhs);
		}
	}

	private DeclarationInformation processDeclInfo(DeclarationInformation declInfo) {
		if (declInfo == null) {
			return null;
		} else if (declInfo.getStorageClass() == DeclarationInformation.StorageClass.GLOBAL) {
			return declInfo;
		} else if (declInfo.getStorageClass() == DeclarationInformation.StorageClass.QUANTIFIED) {
			throw new UnsupportedOperationException("Quantifiers aren't supported yet.");
		} else {
			return new DeclarationInformation(StorageClass.LOCAL, mProcName);
		}
	}
}
