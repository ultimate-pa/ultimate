/**
 * 
 */
package jayhorn.cfg.method;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import jayhorn.cfg.Node;
import jayhorn.cfg.Variable;

/**
 * @author schaef
 *
 */
public class Method implements Node {

	private final String methodName;
	private Variable thisVariable, returnVariable, exceptionalReturnVariable;
	private List<Variable> parameterList;
	private Collection<Variable> locals;
	private Collection<Variable> modifiedGlobals;
	private CfgBlock source;
	private boolean isEntry = false;
	
	public Method(String uniqueName) {
		methodName = uniqueName;
	}

	public String getMethodName() {
		return this.methodName;
	}

	public void initialize(Variable thisVariable, Variable returnVariable,
			Variable exceptionalReturnVariable, List<Variable> parameterList,
			Collection<Variable> locals, CfgBlock source, boolean isEntryPoint) {
		this.thisVariable = thisVariable;
		this.returnVariable = returnVariable;
		this.exceptionalReturnVariable = exceptionalReturnVariable;
		this.parameterList = parameterList;
		this.locals = locals;
		this.source = source;
		this.isEntry = isEntryPoint;
		
		//compute the modifies clause.
		this.modifiedGlobals = new HashSet<Variable>();
		this.modifiedGlobals.addAll(this.getLVariables());
		this.modifiedGlobals.removeAll(locals);
		this.modifiedGlobals.removeAll(parameterList);
		this.modifiedGlobals.remove(exceptionalReturnVariable);
		this.modifiedGlobals.remove(returnVariable);
		this.modifiedGlobals.remove(thisVariable);
	}
	
	public boolean isEntryPoint() {
		return this.isEntry;
	}
	
	public CfgBlock getSource() {
		return this.source;
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
		if (this.modifiedGlobals!=null && this.modifiedGlobals.size()>0) {
			sb.append("\tmodifies: ");
			for (Variable v : this.modifiedGlobals) {
				sb.append(comma);
				sb.append(v.getName());
				comma = ", ";
			}
			sb.append("\n");
		}
		comma = "";
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
	
	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		List<CfgBlock> todo = new LinkedList<CfgBlock>();
		todo.add(this.source);
		Set<CfgBlock> done = new HashSet<CfgBlock>();		
		while (!todo.isEmpty()) {
			CfgBlock current = todo.remove(0);
			done.add(current);
			used.addAll(current.getUsedVariables());
			for (CfgBlock succ : current.getSuccessors()) {
				if (!todo.contains(succ) && !done.contains(succ)) {
					todo.add(succ);
				}
			}
		}
		return used;
	}	
	
	@Override
	public Set<Variable> getLVariables() {
		Set<Variable> used = new HashSet<Variable>();
		List<CfgBlock> todo = new LinkedList<CfgBlock>();
		todo.add(this.source);
		Set<CfgBlock> done = new HashSet<CfgBlock>();		
		while (!todo.isEmpty()) {
			CfgBlock current = todo.remove(0);
			done.add(current);
			used.addAll(current.getLVariables());
			for (CfgBlock succ : current.getSuccessors()) {
				if (!todo.contains(succ) && !done.contains(succ)) {
					todo.add(succ);
				}
			}
		}
		return used;
	}
	
	/**
	 * Return the set of live variable per block.
	 * A variable is live between its first and last use.
	 * TODO: this is not implemented! For each block, it returns all variables.
	 * @return
	 */
	public Map<CfgBlock, Set<Variable>> computeLiveVariables() {
		Map<CfgBlock, Set<Variable>> res = new LinkedHashMap<CfgBlock, Set<Variable>>();
		List<CfgBlock> todo = new LinkedList<CfgBlock>();
		todo.add(this.source);
		Set<CfgBlock> done = new HashSet<CfgBlock>();		
		while (!todo.isEmpty()) {
			CfgBlock current = todo.remove(0);
			done.add(current);
			res.put(current, getUsedVariables());
			for (CfgBlock succ : current.getSuccessors()) {
				if (!todo.contains(succ) && !done.contains(succ)) {
					todo.add(succ);
				}
			}
		}
		return res;
	}
}
