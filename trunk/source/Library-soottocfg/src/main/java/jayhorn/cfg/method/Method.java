/**
 * 
 */
package jayhorn.cfg.method;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import jayhorn.cfg.Node;
import jayhorn.cfg.Variable;
import soot.SootMethod;

/**
 * @author schaef
 *
 */
public class Method implements Node {

	private final String methodName;
	private Variable thisVariable, returnVariable, exceptionalReturnVariable;
	private List<Variable> parameterList;
	private Collection<Variable> locals;
	private CfgBlock source;
	
	public Method(SootMethod m) {
		methodName = m.getDeclaringClass().getName() + "." + m.getName();
	}

	public String getMethodName() {
		return this.methodName;
	}

	public void initialize(Variable thisVariable, Variable returnVariable,
			Variable exceptionalReturnVariable, List<Variable> parameterList,
			Collection<Variable> locals, CfgBlock source) {
		this.thisVariable = thisVariable;
		this.returnVariable = returnVariable;
		this.exceptionalReturnVariable = exceptionalReturnVariable;
		this.parameterList = parameterList;
		this.locals = locals;
		this.source = source;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		sb.append("Method ");
		sb.append(this.methodName);
		String comma = "";
		sb.append("(");
		if (this.thisVariable!=null) {
			sb.append(this.thisVariable.getName());
			comma = ", ";
		}
		for (Variable v : this.parameterList) {
			sb.append(comma);
			sb.append(v.getName());
			comma = ", ";
		}
		sb.append(")\n");
		if (this.returnVariable!=null) {
			sb.append("\treturns: ");
			sb.append(this.returnVariable.getName());
			sb.append("\n");
		}
		sb.append("\tthrows: ");
		sb.append(this.exceptionalReturnVariable.getName());
		sb.append("\n");
		if (!this.locals.isEmpty()) {
			sb.append("\tlocals:\n");
			for (Variable v : this.locals) {
				sb.append("\t\t");
				sb.append(v.getName());
				sb.append("\n");
			}
		}
		
		List<CfgBlock> todo = new LinkedList<CfgBlock>();
		todo.add(this.source);
		Set<CfgBlock> done = new HashSet<CfgBlock>();		
		while (!todo.isEmpty()) {
			CfgBlock current = todo.remove(0);
			done.add(current);
			if (this.source==current) {
				sb.append("Root ->");
			}
			sb.append(current);
			for (CfgBlock succ : current.getSuccessors()) {
				if (!todo.contains(succ) && !done.contains(succ)) {
					todo.add(succ);
				}
			}
		}
		return sb.toString();
	}
	
}
