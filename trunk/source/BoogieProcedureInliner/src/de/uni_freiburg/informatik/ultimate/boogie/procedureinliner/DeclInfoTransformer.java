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
			return new IdentifierExpression(ie.getLocation(), ie.getType(), ie.getIdentifier(),
					processDeclInfo(ie.getDeclarationInformation()));				
		} else {
			return super.processExpression(expr);			
		}
	}
	
	@Override
	public LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			VariableLHS vlhs = (VariableLHS) lhs;
			return new VariableLHS(vlhs.getLocation(), vlhs.getType(), vlhs.getIdentifier(),
					processDeclInfo(vlhs.getDeclarationInformation()));
		} else {
			return lhs;			
		}
	}

	private DeclarationInformation processDeclInfo(DeclarationInformation declInfo) {
		if (declInfo.getStorageClass() == DeclarationInformation.StorageClass.GLOBAL) {
			return declInfo;
		} else if (declInfo.getStorageClass() == DeclarationInformation.StorageClass.QUANTIFIED) {
			throw new UnsupportedOperationException("Quantifiers aren't supported yet.");
		} else {
			return new DeclarationInformation(StorageClass.LOCAL, mProcName);
		}
	}
}
