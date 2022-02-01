package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

import java.util.Collection;
import java.util.Set;

public interface IRemovalInfo<ELEM extends ICongruenceClosureElement<ELEM>> {

	Set<ELEM> getRemovedElements();

	Collection<ELEM> getAlreadyRemovedElements();

}
