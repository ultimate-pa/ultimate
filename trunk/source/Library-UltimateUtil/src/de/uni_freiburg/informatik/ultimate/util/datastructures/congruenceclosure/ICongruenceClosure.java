package de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure;

public interface ICongruenceClosure<ELEM extends ICongruenceClosureElement<ELEM>> {

	IRemovalInfo<ELEM> getElementCurrentlyBeingRemoved();

}
