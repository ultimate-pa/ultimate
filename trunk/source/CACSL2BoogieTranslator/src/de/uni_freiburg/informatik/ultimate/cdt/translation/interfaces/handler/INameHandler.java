/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.NameHandler.Boogie2C;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.IHandler;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 07.03.2012
 */
public interface INameHandler extends IHandler {
    /**
     * Creates an unique (in translation unit) identifier for each variable.
     * 
     * @param scope
     *            should be IASTTranslationUnit, IASTCompoundStatement.
     * @param cId
     *            the name of the C variable.
     * @param compCnt
     *            the counter value of the compoundCntUID
     * @return an unique identifier.
     */
    public String getUniqueIdentifier(IASTNode scope, String cId, int compCnt);

    /**
     * Creates a unique identifier for temporary variables.
     * 
     * @return a unique identifier for temporary variables.
     */
    String getTempVarUID(AUXVAR purpose);

    /**
     * Create identifier for in-parameter of Boogie procedure.
     * @param cid
     * 			 the name of the C procedure parameter
     * @return 
     *    		identifier for in-parameter of Boogie procedure.
     */
	String getInParamIdentifier(String cid);

	Boogie2C getBoogie2C();

	boolean isTempVar(String boogieId);
}
