package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelectOverStore;

/**
 * Union type of ArraySelect and ArraySelectOverStore.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ArrayCellAccess {

	private final ArraySelect mArraySelect;
	private final ArraySelectOverStore mArraySelectOverStore;

	public ArrayCellAccess(final ArraySelect arraySelect) {
		mArraySelect = arraySelect;
		mArraySelectOverStore = null;
	}

	public ArrayCellAccess(final ArraySelectOverStore arraySelectOverStore) {
		mArraySelect = null;
		mArraySelectOverStore = arraySelectOverStore;
	}

	public static List<ArrayCellAccess> extractArrayCellAccesses(final Term formula) {
		final List<ArrayCellAccess> result = new ArrayList<>();

		final Set<String> functionSymbolNames = Collections.singleton("select");

		final ApplicationTermFinder atf = new ApplicationTermFinder(functionSymbolNames, false);
		for (final ApplicationTerm subterm : atf.findMatchingSubterms(formula)) {
			final Term firstParam = subterm.getParameters()[0];
			if (SmtUtils.isFunctionApplication(firstParam, "store")) {
				result.add(new ArrayCellAccess(ArraySelectOverStore.convert(subterm)));
			} else {
				result.add(new ArrayCellAccess(ArraySelect.convert(subterm)));
			}
		}

		return result;
	}

	public Term getArray() {
		// TODO Auto-generated method stub
		return null;
	}

	public Term getIndex() {
		// TODO Auto-generated method stub
		return null;
	}


//	Term getTerm() {
//		if (mArraySelect != null) {
//			return SMT
//		}
//	}
}
