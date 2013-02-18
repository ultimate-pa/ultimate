/**
 * 
 */
package local.stalin.smt.theory.cclosure;

import local.stalin.smt.dpll.SimpleList;


class SeparateInfo extends SimpleList<PairListEntry<CCTerm, CCTerm>> {
	EqualityAtom reason;
}