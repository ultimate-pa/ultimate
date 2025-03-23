package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;

public interface Variable {
	VariableTerm getVariableTerm();

	ExecutionTerm getTerm();

	String getName();

	@Override
	boolean equals(Object b);

	@Override
	int hashCode();

	TermVariable toSMTTerm(final Theory theory);
}