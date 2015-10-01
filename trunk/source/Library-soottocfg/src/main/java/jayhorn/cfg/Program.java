/**
 * 
 */
package jayhorn.cfg;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import jayhorn.cfg.method.Method;
import jayhorn.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class Program {

	private final Map<String, Variable> globalVariables = new HashMap<String, Variable>();
	private final Map<String, Method> methods = new HashMap<String, Method>();
	
	private final Collection<Method> entryPoints = new HashSet<Method>();

	public Variable[] getGlobalVariables() {
		return this.globalVariables.values().toArray(new Variable[this.globalVariables.size()]);
	}
	
	public Variable loopupGlobalVariable(String varName, Type t) {
		if (!this.globalVariables.containsKey(varName)) {
			this.globalVariables.put(varName, new Variable(varName, t));
		}
		return this.globalVariables.get(varName);
	}

	public Method loopupMethod(String methodSignature) {
		if (!methods.containsKey(methodSignature)) {
			Method method = new Method(methodSignature);
			methods.put(methodSignature, method);			
		}
		return methods.get(methodSignature);
	}

	public void addEntryPoint(Method entry) {
		assert(entry.isEntryPoint());
		this.entryPoints.add(entry);
	}
	
	public Method[] getEntryPoints() {
		return entryPoints.toArray(new Method[entryPoints.size()]);
	}
	
}
