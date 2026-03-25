package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public interface Value extends Comparable<Value> {
	BoolValue equals(Value other);

	BoolValue distinct(Value other);

	Object getValue();

	Map<Term, Term> toTerm(final Script script, Term var);

	@Override
	int compareTo(Value b);
}