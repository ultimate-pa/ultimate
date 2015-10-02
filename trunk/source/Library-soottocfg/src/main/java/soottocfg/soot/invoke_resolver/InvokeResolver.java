/**
 * 
 */
package soottocfg.soot.invoke_resolver;

import java.util.List;

import soot.Body;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InstanceInvokeExpr;

/**
 * @author schaef
 *
 */
public abstract class InvokeResolver {

	/**
	 * 
	 */
	public InvokeResolver() {
		// TODO Auto-generated constructor stub
	}

	public abstract List<SootMethod> resolveVirtualCall(Body body, Unit u, InstanceInvokeExpr call);
	
}
