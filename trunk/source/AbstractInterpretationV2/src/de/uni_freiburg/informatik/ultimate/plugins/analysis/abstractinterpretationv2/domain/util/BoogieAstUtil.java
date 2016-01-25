package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;

/**
 * Utility functions for objects from the Boogie abstract syntax tree (AST).
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class BoogieAstUtil {

	public static IBoogieVar createTemporaryIBoogieVar(String identifier, IType type) {
		return new IBoogieVar() {
			@Override
			public String getIdentifier() {
				return identifier;
			}

			@Override
			public IType getIType() {
				return type;
			}

			@Override
			public ApplicationTerm getDefaultConstant() {
				throw new UnsupportedOperationException("Temporary IBoogieVars dont have default constants.");
			}
		};
	}
	
	/**
     * Determines if a {@link IdentifierExpression} references a variable.
     * {@link IdentifierExpression} can also reference functions or procedures.
     * In that case, this method will return {@code false}.
     * 
     * @param ie {@link IdentifierExpression}
     * @return expression references a variable
     */
   public static boolean isVariable(IdentifierExpression ie) {
   	DeclarationInformation di = ie.getDeclarationInformation();
   	switch (di.getStorageClass()) {
   	case PROC_FUNC:
   	case IMPLEMENTATION:
   		return false;
		default:
//		case GLOBAL:
//		case IMPLEMENTATION_INPARAM:
//		case IMPLEMENTATION_OUTPARAM:
//		case LOCAL:
//		case QUANTIFIED:
//		case PROC_FUNC_INPARAM:
//		case PROC_FUNC_OUTPARAM:
			return true;
		}
   }
	
}
