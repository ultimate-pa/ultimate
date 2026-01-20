package de.uni_freiburg.informatik.ultimate.logic;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnifyHash;

public class AssociativeSortSymbol extends SortSymbol
{
	UnifyHash<SortSymbol> functionSortSymbols = new UnifyHash<>();

	public AssociativeSortSymbol(Theory theory, String name, int flags) {
		super(theory, name, 2, null, flags);
	}

	public SortSymbol getAssocFunctionSort(int length) {
		final int hash = length;
		for (final SortSymbol symbol : functionSortSymbols.iterateHashCode(hash)) {
			if (symbol.mNumParams == length) {
				return symbol;
			}
		}
		final String[] names = new String[length];
		for (int i = 0; i < length; i++) {
			names[i] = "x" + i;
		}
		final Sort[] vars = mTheory.createSortVariables(names);
		Sort definition = vars[length - 1];
		for (int i = length - 2; i >= 0; i--) {
			definition = this.getSort(null, vars[i], definition);
		}
		final SortSymbol symbol = new SortSymbol(mTheory, mName, length, definition, mFlags);
		functionSortSymbols.put(hash, symbol);
		return symbol;
	}

	@Override
	public Sort getSort(String[] indices, Sort... args) {
		assert mNumParams == 2;
		if (args.length == 2) {
			return super.getSort(indices, args);
		}

		return getAssocFunctionSort(args.length).getSort(indices, args);
	}
}
