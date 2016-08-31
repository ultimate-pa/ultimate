package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This class is the edge class in a Horn clause graph.
 * It represents a hyper edge that is labelled with a transition formula.
 * The hyper edge may have many sources but has only one target.
 * Additionally there has to be a mapping from the sources to the variables in the
 * transition formula.
 * 
 * (The source is a predicate symbol, so the mapping should say something like
 *  "The variable x in my formula is the i-th argument of the HornClausePredicateSymbol
 *   P that is the j-th source element of this hyper edge" or so..)
 * 
 * @author alex
 *
 */
public class HCGEdge {
	
	Term mFormula;

	HashMap<HornClausePredicateSymbol, Object> mSources;
	HornClausePredicateSymbol mTarget;
	
}
