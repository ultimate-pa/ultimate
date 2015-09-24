/**
 * 
 */
package jayhorn.cfg;

import java.util.HashMap;
import java.util.Map;

import soot.SootMethod;
import jayhorn.cfg.method.Method;
import jayhorn.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class Program {

	private final Map<String, Variable> globalVariables = new HashMap<String, Variable>();
	private final Map<SootMethod, Method> methods = new HashMap<SootMethod, Method>();
	
	public Variable loopupGlobalVariable(String varName, Type t) {
		if (!this.globalVariables.containsKey(varName)) {
			this.globalVariables.put(varName, new Variable(varName, t));
		}
		return this.globalVariables.get(varName);
	}

	public Method loopupMethod(SootMethod m) {
		if (!methods.containsKey(m)) {
			Method method = new Method(m);
			methods.put(m, method);
		}
		return methods.get(m);
	}

}
