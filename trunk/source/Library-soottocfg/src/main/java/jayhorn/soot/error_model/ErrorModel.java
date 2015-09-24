/**
 * 
 */
package jayhorn.soot.error_model;

import jayhorn.cfg.expression.Expression;
import soot.SootClass;

/**
 * @author schaef
 *
 */
public abstract class ErrorModel {

	public abstract void createException(Expression guard, SootClass exception);
	
//	public void createArrayBoundGuard
}
