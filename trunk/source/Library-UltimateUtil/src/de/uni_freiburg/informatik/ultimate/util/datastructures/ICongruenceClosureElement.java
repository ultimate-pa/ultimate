package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Map;
import java.util.Set;

public interface ICongruenceClosureElement<ELEM extends ICongruenceClosureElement<ELEM>> {

	boolean hasSameTypeAs(ELEM other);

	boolean isFunctionApplication();

	ELEM getAppliedFunction();

	ELEM getArgument();

//	void addAfParent(ELEM parent);
//
//	void addArgParent(ELEM parent);
//
//	void removeAfParent(ELEM parent);
//
//	void removeArgParent(ELEM parent);
//
//	Set<ELEM> getAfParents();
//
//	Set<ELEM> getArgParents();

	ELEM replaceAppliedFunction(ELEM replacer);

	ELEM replaceArgument(ELEM replacer);

	ELEM replaceSubNode(Map<ELEM, ELEM> replacementMapping);

//	int getHeight();

	boolean isLiteral();

	boolean isDependent();

	/**
	 * Should only be called if this id is a dependent id. Returns all supporters of this id.
	 * A supporter is an id that a dependent id depends on.
	 * @return
	 */
	Set<ELEM> getSupportingNodes();


}
