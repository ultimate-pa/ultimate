/**
 * 
 */
package soottocfg.soot.invoke_resolver;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import soot.Body;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.ThisRef;

/**
 * @author schaef
 * Resolves virtual calls with using any points-to analysis.
 * This is cheap to compute but a strong over-approximation.
 */
public class DefaultInvokeResolver extends InvokeResolver {

	/* (non-Javadoc)
	 * @see jayhorn.soot.inoke_translation.InvokeTranslation#resolveVirtualCall(soot.jimple.InstanceInvokeExpr)
	 */
	@Override
	public List<SootMethod> resolveVirtualCall(Body body, Unit u, InstanceInvokeExpr call) {
		SootMethod callee = call.getMethod();
		SootClass sc = callee.getDeclaringClass();
		Value base = call.getBase();

		List<SootMethod> res = new LinkedList<SootMethod>();
		// if its a call to "this", don't try anything fancy.
		if (base instanceof ThisRef || base == body.getThisLocal()) {
			res.add(callee);
		} else {
			Collection<SootClass> possibleClasses;
			if (sc.isInterface()) {
				possibleClasses = Scene.v().getFastHierarchy()
						.getAllImplementersOfInterface(sc);
			} else {
				possibleClasses = Scene.v().getFastHierarchy()
						.getSubclassesOf(sc);
			}
			for (SootClass sub : possibleClasses) {
				if (sub.resolvingLevel() < SootClass.SIGNATURES) {
					// Log.error("Not checking subtypes of " + sub.getName());
					// Then we probably really don't care.
				} else {
					if (sub.declaresMethod(callee.getName(),
							callee.getParameterTypes(), callee.getReturnType())) {
						res.add(sub.getMethod(callee.getName(),
								callee.getParameterTypes(),
								callee.getReturnType()));
					}
				}
			}
		}

		// TODO: we have to sort the methods by type.
		return res;	
	}

}
