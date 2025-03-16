package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;

public class Constraint {
	private final Variable variable;
	private final ExecutionTerm constraint;
	public final RelationSymbol relation;

	public Constraint(final Variable mVariable, final ExecutionTerm mConstraint, final RelationSymbol mRelation) {
		variable = mVariable;
		constraint = mConstraint;
		relation = mRelation;
		assert variable.getTerm().returnType == constraint.returnType;
		assert constraint.getVariables().size() == 0;
	}

	@Override
	public String toString() {
		return variable.getTerm() + " " + relation + " " + constraint;
	}

	public Variable getVariable() {
		return variable;
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof Constraint)) {
			return false;
		}
		final Constraint bCast = (Constraint) b;
		return variable.getTerm().equals(bCast.variable.getTerm()) && constraint.equals(bCast.constraint)
				&& relation.equals(bCast.relation);
	}

	public ExecutionTerm getConstraint() {
		return constraint;
	}
}