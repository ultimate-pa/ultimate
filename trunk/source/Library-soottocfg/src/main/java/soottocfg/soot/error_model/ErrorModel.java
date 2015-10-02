/**
 * 
 */
package soottocfg.soot.error_model;

import soot.SootClass;
import soottocfg.cfg.expression.Expression;

/**
 * @author schaef
 *
 */
public abstract class ErrorModel {

	public abstract void createException(Expression guard, SootClass exception);
	
//	public void createArrayBoundGuard
}
