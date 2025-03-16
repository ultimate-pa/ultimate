package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class Arc {
	private final ExecutionTerm variableTerm;
	private final Variable variable;
	private final ExecutionTerm constraint;
	public final RelationSymbol relation;
	private final HashSet<Variable> variables;

	public Arc(final Variable mVariable, final ExecutionTerm mConstraint, final RelationSymbol mRelation) {
		variableTerm = mVariable.getTerm();
		variable = mVariable;
		constraint = mConstraint;
		relation = mRelation;
		assert variable.getTerm().returnType == constraint.returnType;
		variables = constraint.getVariables();
		assert variables.size() > 0;
	}

	public Variable getDefinedVariable() {
		return variable;
	}

	protected HashSet<Variable> getVariables() {
		return variables;
	}

	@Override
	public String toString() {
		return variableTerm + " " + relation + " " + constraint;
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof Arc)) {
			return false;
		}
		final Arc bCast = (Arc) b;
		return variableTerm.equals(bCast.variableTerm) && constraint.equals(bCast.constraint)
				&& relation.equals(bCast.relation);
	}

	public ExecutionTerm getConstraint() {
		return constraint;
	}
}