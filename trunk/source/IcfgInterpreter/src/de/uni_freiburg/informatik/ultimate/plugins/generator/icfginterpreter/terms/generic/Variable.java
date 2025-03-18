package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.Domain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;

public interface Variable/* <T extends Domain<T>> */ {
	VariableTerm getVariableTerm();

	ExecutionTerm getTerm();

	String getName();

	Domain<?> getDomain();

	@Override
	boolean equals(Object b);

	@Override
	int hashCode();

	TermVariable toSMTTerm(final Theory theory);
}