package de.uni_freiburg.informatik.ultimate.util.datastructures;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure.RemoveElement;

public interface ICongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM>> {

	RemoveElement<ELEM> getElementCurrentlyBeingRemoved();

}
