/**
 * 
 */
package jayhorn.cfg.method;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import jayhorn.cfg.Node;
import jayhorn.cfg.Variable;
import jayhorn.cfg.expression.Expression;
import jayhorn.cfg.statement.Statement;
import jayhorn.soot.util.SootTranslationHelpers;

/**
 * @author schaef
 *
 */
public class CfgBlock implements Node {

	protected final String label;
	
	
	protected final List<CfgBlock> successors;
	protected final List<Statement> statements;
	protected final Map<CfgBlock, Expression> successorConditions;
	
	public CfgBlock() {
		this.label = "Block"+(SootTranslationHelpers.v().getUniqueNumber());
		
		this.successors = new LinkedList<CfgBlock>();
		this.statements = new LinkedList<Statement>();
		this.successorConditions = new HashMap<CfgBlock, Expression>();
	}
	
	public String getLabel() {
		return this.label;
	}
	
	public void addStatement(Statement s) {
		this.statements.add(s);
	}
	
	public List<Statement> getStatements() {
		return this.statements;
	}
	
	public void addSuccessor(CfgBlock suc) {
		if (this.successors.contains(suc)) {
			throw new RuntimeException("Already connected");
		}
		this.successors.add(suc);
	}

	public void addConditionalSuccessor(Expression condition, CfgBlock suc) {
		if (this.successors.contains(suc)) {
			throw new RuntimeException("Already connected");
		}		
		this.successors.add(suc);
		this.successorConditions.put(suc, condition);
	}
	
	public List<CfgBlock> getSuccessors() {
		return this.successors;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(this.label);
		sb.append(":\n");
		for (Statement s : this.statements) {
			sb.append("(ln ");
			sb.append(s.getJavaSourceLine());
			sb.append(")\t");
			sb.append(s.toString());
			sb.append("\n");
		}
		if (!this.successors.isEmpty()) {
			sb.append("\tgoto:\n");
			for (CfgBlock suc : this.successors) {
				sb.append("\t  ");
				if (this.successorConditions.containsKey(suc)) {
					sb.append("if ");
					sb.append(this.successorConditions.get(suc));
					sb.append(": ");
				}
				sb.append(suc.getLabel());
				sb.append("\n");
			}
		} else {
			sb.append("\treturn\n");
		}
		return sb.toString();
	}
	
	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		for (Statement s : statements) {
			used.addAll(s.getUsedVariables());
		}
		//TODO: do the variables in the conditional belong to this block?
		for (Entry<CfgBlock, Expression> entry : successorConditions.entrySet()) {
			used.addAll(entry.getValue().getUsedVariables());
		}
		return used;
	}
	
	@Override
	public Set<Variable> getLVariables() {
		Set<Variable> used = new HashSet<Variable>();
		for (Statement s : statements) {
			used.addAll(s.getLVariables());
		}
		return used;
	}	
	
}
